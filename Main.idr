module Main

import Data.Fin

foo : Nat -> Nat
foo k = ?foo_rhs

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

data SaveConvention : Type where
  SaveNone   : SaveConvention
  SaveCaller : SaveConvention
  SaveCallee : SaveConvention

data OwnerConvention : Type where
  OwnerUser      : OwnerConvention
  OwnerKernel    : OwnerConvention
  OwnerAssembler : OwnerConvention

Convention : Type
Convention = (SaveConvention, OwnerConvention)

data Reg : Convention -> Type where
  RegZero : Reg (SaveNone, OwnerUser)
  RegAT   : Reg (SaveNone, OwnerUser)
  RegGP   : Reg (SaveNone, OwnerUser)
  RegSP   : Reg (SaveNone, OwnerUser)
  RegFP   : Reg (SaveNone, OwnerUser)
  RegRA   : Reg (SaveNone, OwnerUser)
  RegV    : Fin 2 -> Reg (SaveNone, OwnerUser)
  RegA    : Fin 4 -> Reg (SaveNone, OwnerUser)
  RegT    : Fin 10 -> Reg (SaveNone, OwnerUser)
  RegS    : Fin 8 -> Reg (SaveNone, OwnerUser)
  RegK    : Fin 2 -> Reg (SaveNone, OwnerUser)

data Imm : Type where
  Immediate : Imm

data Off : Type where
  Offset : Off

data Lab : Type where
  Label : Lab

data Instruction : Type where
  SPIM_ADD    : Reg c1 -> Reg c2 -> Reg c3 -> Instruction
  SPIM_ADDU   : Reg c1 -> Reg c2 -> Reg c3 -> Instruction
  SPIM_ADDI   : Reg c1 -> Reg c2 -> Imm    -> Instruction
  SPIM_SUB    : Reg c1 -> Reg c2 -> Reg c3 -> Instruction
  SPIM_SUBU   : Reg c1 -> Reg c2 -> Reg c3 -> Instruction
  SPIM_DIV    : Reg c1 -> Reg c2           -> Instruction
  SPIM_DIVU   : Reg c1 -> Reg c2           -> Instruction
  SPIM_MULT   : Reg c1 -> Reg c2           -> Instruction
  SPIM_MULTU  : Reg c1 -> Reg c2           -> Instruction
  SPIM_AND    : Reg c1 -> Reg c2 -> Reg c3 -> Instruction
  SPIM_ANDI   : Reg c1 -> Reg c2 -> Imm    -> Instruction
  SPIM_NOR    : Reg c1 -> Reg c2 -> Reg c3 -> Instruction
  SPIM_OR     : Reg c1 -> Reg c2 -> Reg c3 -> Instruction
  SPIM_ORI    : Reg c1 -> Reg c2 -> Imm    -> Instruction
  SPIM_XOR    : Reg c1 -> Reg c2 -> Reg c3 -> Instruction
  SPIM_XORI   : Reg c1 -> Reg c2 -> Imm    -> Instruction
  SPIM_SLL    : Reg c1 -> Reg c2 -> Imm    -> Instruction
  SPIM_SLLV   : Reg c1 -> Reg c2 -> Reg c3 -> Instruction
  SPIM_SRL    : Reg c1 -> Reg c2 -> Imm    -> Instruction
  SPIM_SRLV   : Reg c1 -> Reg c2 -> Reg c3 -> Instruction
  SPIM_MFLO   : Reg c1                     -> Instruction
  SPIM_MFHI   : Reg c1                     -> Instruction
  SPIM_LUI    : Reg c1 -> Imm              -> Instruction
  SPIM_LB     : Reg c1 -> Off    -> Reg c3 -> Instruction
  SPIM_LW     : Reg c1 -> Off    -> Reg c3 -> Instruction
  SPIM_SB     : Reg c1 -> Off    -> Reg c3 -> Instruction
  SPIM_SW     : Reg c1 -> Off    -> Reg c3 -> Instruction
  SPIM_SLT    : Reg c1 -> Reg c2 -> Reg c3 -> Instruction
  SPIM_SLTU   : Reg c1 -> Reg c2 -> Reg c3 -> Instruction
  SPIM_SLTI   : Reg c1 -> Reg c2 -> Imm    -> Instruction
  SPIM_BEQ    : Reg c1 -> Reg c2 -> Lab    -> Instruction
  SPIM_BNE    : Reg c1 -> Reg c2 -> Lab    -> Instruction
  SPIM_BGEZ   : Reg c1 -> Lab              -> Instruction
  SPIM_BGTZ   : Reg c1 -> Lab              -> Instruction
  SPIM_BLEZ   : Reg c1 -> Lab              -> Instruction
  SPIM_BLTZ   : Reg c1 -> Lab              -> Instruction
  SPIM_BLTZAL : Reg c1 -> Lab              -> Instruction
  SPIM_BGEZAL : Reg c1 -> Lab              -> Instruction
  SPIM_J      : Lab                        -> Instruction
  SPIM_JAL    : Lab                        -> Instruction
  SPIM_JR     : Reg c1                     -> Instruction
  SPIM_JALR   : Reg c1                     -> Instruction
