module Register

import Data.Fin
--import Mush

%default total

-- ---- REGISTERS ----
--
-- zero
-- at (assembler temporary)
-- v0, v1 (return registers)
-- a0 - a3 (argument registers)
-- t0 - t7 (caller saved)
-- s0 - s7 (callee saved)
-- t8, t9 (caller saved)
-- k0, k1 (OS reserved)
-- gp (global area pointer)
-- sp (stack pointer)
-- fp (frame pointer)
-- ra (return address)

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

-- register : (f : Fin 32) -> registerToFin (registerFromFin f) = f
-- register = ?register
