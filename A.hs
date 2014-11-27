{-# LANGUAGE RankNTypes, DataKinds, KindSignatures, GADTs, EmptyDataDecls, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeOperators, TypeFamilies, Arrows, ViewPatterns, AllowAmbiguousTypes, UndecidableInstances, ScopedTypeVariables, IncoherentInstances #-}
module Main where

import Prelude hiding (id, (.))

import Control.Monad
import Control.Applicative
import Control.Category
import Control.Arrow
  
import Data.Proxy
import Unsafe.Coerce

import Data.Type.Equality

import qualified GHC.TypeLits as GHC

-- Nats

data Nat = Zero | Succ Nat

data SNat :: Nat -> * where
  SZero :: SNat Zero
  SSucc :: SNat n -> SNat (Succ n)

type family (a :: Nat) + (b :: Nat) :: Nat where
  Zero   + b = b
  Succ a + b = Succ (a + b)

(%+) :: SNat a -> SNat b -> SNat (a + b)
SZero   %+ b = b
SSucc a %+ b = SSucc (a %+ b)

plusAssociative :: SNat a -> SNat b -> SNat c -> ((a+b)+c) :~: (a+(b+c))
plusAssociative SZero b c     = Refl
plusAssociative (SSucc a) b c = case plusAssociative a b c of
  Refl -> Refl

plus_0_right_neutral :: SNat a -> (a + Zero) :~: a
plus_0_right_neutral SZero     = Refl
plus_0_right_neutral (SSucc a) = case plus_0_right_neutral a of
  Refl -> Refl

type family (a :: Nat) - (b :: Nat) :: Nat where
  a      - Zero   = a
  Zero   - a      = Zero
  Succ a - Succ b = a - b

type family (a :: Nat) * (b :: Nat) :: Nat where
  Zero   * b = Zero
  Succ a * b = b + (a * b)

(%*) :: SNat a -> SNat b -> SNat (a * b)
SZero   %* _ = SZero
SSucc a %* b = b %+ (a %* b)

type family (a :: Nat) ^ (b :: Nat) :: Nat where
  a ^ Zero   = Succ Zero
  a ^ Succ b = a * (a ^ b)

(%^) :: SNat a -> SNat b -> SNat (a ^ b)
a %^ SZero   = SSucc SZero
a %^ SSucc b = a %* (a %^ b)

type family Half (a :: Nat) :: Nat where
  Half Zero            = Zero
  Half (Succ Zero)     = Zero
  Half (Succ (Succ a)) = Succ (Half a)

-- Vector

data Vector n a where
  Nil  :: Vector Zero a
  (:>) :: a -> Vector n a -> Vector (Succ n) a

infixr 5 :>
append :: Vector n a -> Vector m a -> Vector (n + m) a
append Nil ys       = ys
append (x :> xs) ys = x :> append xs ys

-- Circuit Arrow

newtype CircuitA m a b = CircuitA (a -> m b)

instance Monad m => Category (CircuitA m) where
  id                      = CircuitA return
  CircuitA f . CircuitA g = CircuitA (f <=< g)

instance Monad m => Arrow (CircuitA m) where
  arr                 = CircuitA . (return .)
  first (CircuitA f)  = CircuitA $ \(a, b)  -> do
    a' <- f a
    return (a', b)
  second (CircuitA f) = CircuitA $ \(a, b) -> do
    b' <- f b
    return (a, b')

instance (Applicative m, Monad m) => ArrowChoice (CircuitA m) where
  left c = CircuitA $ \x -> case x of
    Left a  -> fmap Left $ c -$- a
    Right b -> return . Right $ b

-- -- Signal

infixr 5 :.:

data Empty where { }
data a :.: b where { }
data Bit where { }
data BitVector (n :: Nat) where { }

data BitVector' (n :: Nat) where { }

class SignalType s where
  data Signal s
instance SignalType Bit where
  data Signal Bit = SBit { unSBit :: Int }
instance SignalType (BitVector n) where
  data Signal (BitVector n) = SBitVector { unSBitVector :: Int }
instance SignalType Empty where
  data Signal Empty = SEmpty
instance (SignalType a, SignalType b) => SignalType (a :.: b) where
  data Signal (a :.: b) = Signal a :.: Signal b
instance SignalType (BitVector' n) where
  data Signal (BitVector' n) = SBitVector' (Vector n (Signal Bit))

class SignalType s => BitWise s where
  bitwise :: (Applicative m, Monad m) => (Circuit m (Bit :.: Bit) Bit) -> Circuit m (s :.: s) s
instance BitWise Bit where
  bitwise c = c
instance BitWise Empty where
  bitwise _ = proc _ -> returnA -< SEmpty
instance (BitWise a, BitWise b) => BitWise (a :.: b) where
  bitwise c = proc ((a :.: b) :.: (a' :.: b')) -> do
    a'' <- bitwise c -< a :.: a'
    b'' <- bitwise c -< b :.: b'
    returnA         -< a'' :.: b''
instance BitWise (BitVector' n) where
  bitwise = CircuitA . pouet
    where
      pouet :: (Applicative m, Monad m) => Circuit m (Bit :.: Bit) Bit -> Signal (BitVector' n :.: BitVector' n) -> m (Signal (BitVector' n))
      pouet c (SBitVector' Nil :.: SBitVector' Nil)             = return $ SBitVector' Nil
      pouet c (SBitVector' (x :> xs) :.: SBitVector' (y :> ys)) = do
        z <- bitwise c -$- (x :.: y)
        SBitVector' zs <- bitwise c -$- (SBitVector' xs :.: SBitVector' ys)
        return $ SBitVector' (z :> zs)

-- class ViewBV (n :: Nat) (a :: Nat) where
--   viewBV :: Signal (BitVector' n) -> (Signal (BitVector' a), Signal (BitVector' (n - a)))
-- instance ViewBV n Zero where
--   viewBV (SBitVector' xs) = (SBitVector' Nil, SBitVector' xs)
-- instance ViewBV Zero a where
-- instance ViewBV (Succ n) (Succ a) where
--   viewBV (SBitVector' (x :> xs)) =
--     let (SBitVector' ys, zs) = viewBV (SBitVector' xs) in
--      (SBitVector' (x :> ys), zs)
-- instance ViewBV n a where

viewBV :: SNat a -> SNat b -> Signal (BitVector' (a + b)) -> (Signal (BitVector' a), Signal (BitVector' b))
viewBV SZero _     bv                      = (SBitVector' Nil, bv)
viewBV (SSucc a) b (SBitVector' (x :> xs)) =
  case viewBV a b (SBitVector' xs) of
   (SBitVector' ys, bv') -> (SBitVector' (x :> ys), bv')
                   
-- -- Circuit

type Circuit m a b = CircuitA m (Signal a) (Signal b)

infixr 1 -$-
(-$-) :: CircuitA m a b -> a -> m b
CircuitA f -$- a = f a

infixr 4 -&-
(-&-) :: Monad m => Circuit m a b -> Circuit m a c -> Circuit m a (b :.: c)
a -&- b = CircuitA $ \x -> do
  (a', b') <- a &&& b -$- x
  return (a' :.: b')
  
infixr 4 -*-
(-*-) :: Monad m => Circuit m a c -> Circuit m b d -> Circuit m (a :.: b) (c :.: d)
a -*- b = CircuitA $ \(x :.: y) -> do
  (a', b') <- a *** b -$- (x, y)
  return (a' :.: b')

class (Applicative m, Monad m) => CircuitMonad m where
  zero                   :: Circuit m Empty Bit
  one                    :: Circuit m Empty Bit
  constant               :: Vector n Bool -> Circuit m Empty (BitVector n)
  not1                   :: Circuit m Bit Bit
  and2, xor2, or2, nand2 :: Circuit m (Bit :.: Bit) Bit
  mux3                   :: Circuit m (Bit :.: Bit :.: Bit) Bit

  --concat2                :: Circuit m (BitVector a :.: BitVector b) (BitVector (a + b))
  --select                 :: (i + 1 <= n) => Proxy i -> Circuit m (BitVector n) Bit
  --slice                  :: (i + 1 <= n, i <= j, j + 1 <= n) => Proxy i -> Proxy j -> Circuit m (BitVector n) (BitVector (j - i + 1))

  reg                    :: (Circuit m Empty Bit -> Circuit m a Bit) -> Circuit m a Bit

  rom                    :: Circuit m (BitVector as) (BitVector ws)
  ram                    :: (Circuit m (BitVector as) (BitVector ws) -> Circuit m a (Bit, BitVector as, BitVector ws)) -> Circuit m a (BitVector ws)

-- -- Examples

-- halfAdder :: CircuitMonad m => Circuit m (Bit :.: Bit) (Bit :.: Bit)
-- halfAdder = xor2 -&- and2

-- fullAdder :: CircuitMonad m => Circuit m (Bit :.: Bit :.: Bit) (Bit :.: Bit)
-- fullAdder = proc (a :.: b :.: c) -> do
--   s1 :.: r1 <- halfAdder -< a :.: b
--   s2 :.: r2 <- halfAdder -< s1 :.: c
--   r         <- xor2      -< r1 :.: r2
--   returnA               -< s2 :.: r

-- cm2 :: CircuitMonad m => Circuit m Empty Bit
-- cm2 = reg $ \prev -> not1 . prev

-- andBitwise :: (CircuitMonad m, BitWise a) => Circuit m (a :.: a) a
-- andBitwise = bitwise and2

-- concat3 :: CircuitMonad m => Circuit m (BitVector a :.: BitVector b :.: BitVector c) (BitVector (a + b + c))
-- concat3 = proc (a :.: b :.: c) -> do
--   ab  <- concat2 -< a  :.: b
--   abc <- concat2 -< ab :.:  c
--   returnA       -< abc

-- mux :: (CircuitMonad m, BitWise a) => Circuit m (Bit :.: a :.: a) a
-- mux = CircuitA $ \(a :.: b :.: c) -> do
--   bitwise (proc (x :.: y) -> mux3 -< (a :.: x :.: y)) -$- (b :.: c)

two = SSucc (SSucc SZero)
four = two %+ two

allBV :: CircuitMonad m => SNat n -> Circuit m (BitVector' (Succ (Succ Zero) ^ n)) Bit
allBV SZero     = CircuitA $ \(SBitVector' (x :> Nil)) -> return x
allBV (SSucc n) =
  case plus_0_right_neutral ((two %^ n) %+ (two %^ n)) of
   Refl -> case plusAssociative (two %^ n) (two %^ n) SZero of
            Refl -> proc (viewBV (two %^ n) (two %^ n) -> (a, b)) -> do
              and2 . (allBV n -*- allBV n)  -< a :.: b

pouet :: CircuitMonad m => Circuit m (BitVector' (Succ (Succ (Succ (Succ Zero))))) Bit
pouet = allBV two

instance CircuitMonad IO where
  zero = CircuitA $ \SEmpty -> do
    putStrLn "zero"
    return (SBit 0)
  one = CircuitA $ \SEmpty -> do
    putStrLn "one"
    return (SBit 1)
  and2 = CircuitA $ \(SBit x :.: SBit y) -> do
    putStrLn "and"
    return (SBit (x + y))

main :: IO ()
main = do
  pouet -$- SBitVector' (SBit 5 :> SBit 4 :> SBit 9 :> SBit 46 :> Nil)
  return ()
