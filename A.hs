{-# LANGUAGE RankNTypes, DataKinds, KindSignatures, GADTs, EmptyDataDecls, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeOperators, TypeFamilies, Arrows, ViewPatterns, AllowAmbiguousTypes, UndecidableInstances, ScopedTypeVariables, IncoherentInstances #-}
module A where

import Prelude hiding (id, (.))

import Control.Monad
import Control.Applicative
import Control.Category
import Control.Arrow
  
import Data.Proxy
import Unsafe.Coerce

-- Nats

data Nat = Zero | Succ Nat

type family (a :: Nat) + (b :: Nat) :: Nat
type instance Zero   + b = b
type instance Succ a + b = Succ (a + b)

type family (a :: Nat) - (b :: Nat) :: Nat
type instance a - Zero        = a
type instance Zero - a        = Zero
type instance Succ a - Succ b = a - b

type family (a :: Nat) * (b :: Nat) :: Nat
type instance Zero     * b = Zero
type instance (Succ a) * b = b + (a * b)

type family (a :: Nat) ^ (b :: Nat) :: Nat
type instance a ^ Zero   = Succ Zero
type instance a ^ Succ b = a * (a ^ b)

type family Half (a :: Nat) :: Nat
type instance Half Zero            = Zero
type instance Half (Succ Zero)     = Zero
type instance Half (Succ (Succ a)) = Succ (Half a)

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

class ViewBV (n :: Nat) (a :: Nat) where
  viewBV :: Signal (BitVector' n) -> (Signal (BitVector' a), Signal (BitVector' (n - a)))
instance ViewBV n Zero where
  viewBV (SBitVector' xs) = (SBitVector' Nil, SBitVector' xs)
instance ViewBV Zero a where
instance ViewBV (Succ n) (Succ a) where
  viewBV (SBitVector' (x :> xs)) =
    let (SBitVector' ys, zs) = viewBV (SBitVector' xs) in
     (SBitVector' (x :> ys), zs)
instance ViewBV n a where

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

class AllBV (n :: Nat) where
  allBV :: CircuitMonad m => Circuit m (BitVector' n) Bit
instance AllBV Zero where
  allBV = undefined
instance AllBV (Succ n) where
  allBV = CircuitA $ \(viewBV -> (xs :: Signal (BitVector' (Half (Succ n))), unsafeCoerce -> ys :: Signal (BitVector' (Half (Succ n))))) -> do
    x <- allBV -$- xs
    y <- allBV -$- ys
    and2 -$- x :.: y
instance AllBV n where

pou :: CircuitMonad m => Circuit m (BitVector' (Succ (Succ Zero))) Bit
pou = allBV

