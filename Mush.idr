module Mush

import Language.Reflection
import Pruviloj.Core
import Pruviloj.Induction
import Data.Fin
import Derive.Eq

%default total

public export
data Reg : Type where
  RegZero : Reg
  RegAT   : Reg
  RegGP   : Reg
  RegSP   : Reg
  RegFP   : Reg
  RegRA   : Reg
  RegV0   : Reg
  RegV1   : Reg
  RegA0   : Reg
  RegA1   : Reg
  RegA2   : Reg
  RegA3   : Reg
  RegT0   : Reg
  RegT1   : Reg
  RegT2   : Reg
  RegT3   : Reg
  RegT4   : Reg
  RegT5   : Reg
  RegT6   : Reg
  RegT7   : Reg
  RegT8   : Reg
  RegT9   : Reg
  RegS0   : Reg
  RegS1   : Reg
  RegS2   : Reg
  RegS3   : Reg
  RegS4   : Reg
  RegS5   : Reg
  RegS6   : Reg
  RegS7   : Reg
  RegK0   : Reg
  RegK1   : Reg

derive Eq for Reg

public export
registerFromFin : Fin 32 -> Reg
registerFromFin f = helper (finToInteger f)
  where
    partial
    helper : Integer -> Reg
    helper 0  = RegZero
    helper 1  = RegAT
    helper 2  = RegV0
    helper 3  = RegV1
    helper 4  = RegA0
    helper 5  = RegA1
    helper 6  = RegA2
    helper 7  = RegA3
    helper 8  = RegT0
    helper 9  = RegT1
    helper 10 = RegT2
    helper 11 = RegT3
    helper 12 = RegT4
    helper 13 = RegT5
    helper 14 = RegT6
    helper 15 = RegT7
    helper 16 = RegS0
    helper 17 = RegS1
    helper 18 = RegS2
    helper 19 = RegS3
    helper 20 = RegS4
    helper 21 = RegS5
    helper 22 = RegS6
    helper 23 = RegS7
    helper 24 = RegT8
    helper 25 = RegT9
    helper 26 = RegK0
    helper 27 = RegK1
    helper 28 = RegGP
    helper 29 = RegSP
    helper 30 = RegFP
    helper 31 = RegRA
    helper _  = assert_unreachable

public export
registerToFin : Reg -> Fin 32
registerToFin RegZero = restrict 31 0
registerToFin RegAT   = restrict 31 1
registerToFin RegV0   = restrict 31 2
registerToFin RegV1   = restrict 31 3
registerToFin RegA0   = restrict 31 4
registerToFin RegA1   = restrict 31 5
registerToFin RegA2   = restrict 31 6
registerToFin RegA3   = restrict 31 7
registerToFin RegT0   = restrict 31 8
registerToFin RegT1   = restrict 31 9
registerToFin RegT2   = restrict 31 10
registerToFin RegT3   = restrict 31 11
registerToFin RegT4   = restrict 31 12
registerToFin RegT5   = restrict 31 13
registerToFin RegT6   = restrict 31 14
registerToFin RegT7   = restrict 31 15
registerToFin RegT8   = restrict 31 24
registerToFin RegT9   = restrict 31 25
registerToFin RegS0   = restrict 31 16
registerToFin RegS1   = restrict 31 17
registerToFin RegS2   = restrict 31 18
registerToFin RegS3   = restrict 31 19
registerToFin RegS4   = restrict 31 20
registerToFin RegS5   = restrict 31 21
registerToFin RegS6   = restrict 31 22
registerToFin RegS7   = restrict 31 23
registerToFin RegK0   = restrict 31 26
registerToFin RegK1   = restrict 31 27
registerToFin RegGP   = restrict 31 28
registerToFin RegSP   = restrict 31 29
registerToFin RegFP   = restrict 31 30
registerToFin RegRA   = restrict 31 31

public export
auto : Elab ()
auto = do
  compute
  attack
  try intros
  hs <- map fst <$> getEnv
  for_ hs $
    \ih => try (rewriteWith (Var ih))
  hypothesis <|> search
  solve

public export
mush : Elab ()
mush = assert_total $ do
  attack
  x <- gensym "x"
  intro x
  try intros
  induction (Var x) `andThen` auto
  solve


public export
proveRegister : Elab ()
proveRegister = do
  mush

-- register : registerToFin (registerFromFin (FS (FS (FS FZ)))) = (FS (FS (FS FZ)))
-- register = %runElab (do { compute; triv; })

record Iso (a : Type) (b : Type) where
  constructor MkPS
  to : a -> b
  from : b -> a
  inverseL : (x : a) -> from (to x) = x
  inverseR : (y : b) -> to (from y) = y

registerAdjoint1 : (r : Reg) -> (registerFromFin (registerToFin r) = r)
registerAdjoint1 RegZero = ?registerAdjoint1_1
registerAdjoint1 RegAT = ?registerAdjoint1_2
registerAdjoint1 RegGP = ?registerAdjoint1_3
registerAdjoint1 RegSP = ?registerAdjoint1_4
registerAdjoint1 RegFP = ?registerAdjoint1_5
registerAdjoint1 RegRA = ?registerAdjoint1_6
registerAdjoint1 RegV0 = ?registerAdjoint1_7
registerAdjoint1 RegV1 = ?registerAdjoint1_8
registerAdjoint1 RegA0 = ?registerAdjoint1_9
registerAdjoint1 RegA1 = ?registerAdjoint1_10
registerAdjoint1 RegA2 = ?registerAdjoint1_11
registerAdjoint1 RegA3 = ?registerAdjoint1_12
registerAdjoint1 RegT0 = ?registerAdjoint1_13
registerAdjoint1 RegT1 = ?registerAdjoint1_14
registerAdjoint1 RegT2 = ?registerAdjoint1_15
registerAdjoint1 RegT3 = ?registerAdjoint1_16
registerAdjoint1 RegT4 = ?registerAdjoint1_17
registerAdjoint1 RegT5 = ?registerAdjoint1_18
registerAdjoint1 RegT6 = ?registerAdjoint1_19
registerAdjoint1 RegT7 = ?registerAdjoint1_20
registerAdjoint1 RegT8 = ?registerAdjoint1_21
registerAdjoint1 RegT9 = ?registerAdjoint1_22
registerAdjoint1 RegS0 = ?registerAdjoint1_23
registerAdjoint1 RegS1 = ?registerAdjoint1_24
registerAdjoint1 RegS2 = ?registerAdjoint1_25
registerAdjoint1 RegS3 = ?registerAdjoint1_26
registerAdjoint1 RegS4 = ?registerAdjoint1_27
registerAdjoint1 RegS5 = ?registerAdjoint1_28
registerAdjoint1 RegS6 = ?registerAdjoint1_29
registerAdjoint1 RegS7 = ?registerAdjoint1_30
registerAdjoint1 RegK0 = ?registerAdjoint1_31
registerAdjoint1 RegK1 = ?registerAdjoint1_32

-- Example of use
private
plusAssoc : (j, k, l : Nat) -> plus (plus j k) l = plus j (plus k l)
plusAssoc = %runElab mush

