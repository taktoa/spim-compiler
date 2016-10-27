module Main

import Data.Bits
import Data.Fin
import Data.Vect
import Data.SortedMap
import Control.Monad.State
import Register

--%default total


data Imm : Type where
  MkImm : Bits32 -> Imm

data Off : Type where
  MkOff : Bits32 -> Off

data Addr : Type where
  MkAddr : Bits32 -> Addr

data Lab : Type where
  MkLab : String -> Lab

data Instruction : Type where
  SPIM_ADD    : Reg -> Reg -> Reg -> Instruction
  SPIM_ADDU   : Reg -> Reg -> Reg -> Instruction
  SPIM_ADDI   : Reg -> Reg -> Imm -> Instruction
  SPIM_SUB    : Reg -> Reg -> Reg -> Instruction
  SPIM_SUBU   : Reg -> Reg -> Reg -> Instruction
  SPIM_DIV    : Reg -> Reg        -> Instruction
  SPIM_DIVU   : Reg -> Reg        -> Instruction
  SPIM_MULT   : Reg -> Reg        -> Instruction
  SPIM_MULTU  : Reg -> Reg        -> Instruction
  SPIM_AND    : Reg -> Reg -> Reg -> Instruction
  SPIM_ANDI   : Reg -> Reg -> Imm -> Instruction
  SPIM_NOR    : Reg -> Reg -> Reg -> Instruction
  SPIM_OR     : Reg -> Reg -> Reg -> Instruction
  SPIM_ORI    : Reg -> Reg -> Imm -> Instruction
  SPIM_XOR    : Reg -> Reg -> Reg -> Instruction
  SPIM_XORI   : Reg -> Reg -> Imm -> Instruction
  SPIM_SLL    : Reg -> Reg -> Imm -> Instruction
  SPIM_SLLV   : Reg -> Reg -> Reg -> Instruction
  SPIM_SRL    : Reg -> Reg -> Imm -> Instruction
  SPIM_SRLV   : Reg -> Reg -> Reg -> Instruction
  SPIM_MFLO   : Reg               -> Instruction
  SPIM_MFHI   : Reg               -> Instruction
  SPIM_LUI    : Reg -> Imm        -> Instruction
  SPIM_LB     : Reg -> Off -> Reg -> Instruction
  SPIM_LW     : Reg -> Off -> Reg -> Instruction
  SPIM_SB     : Reg -> Off -> Reg -> Instruction
  SPIM_SW     : Reg -> Off -> Reg -> Instruction
  SPIM_SLT    : Reg -> Reg -> Reg -> Instruction
  SPIM_SLTU   : Reg -> Reg -> Reg -> Instruction
  SPIM_SLTI   : Reg -> Reg -> Imm -> Instruction
  SPIM_BEQ    : Reg -> Reg -> Lab -> Instruction
  SPIM_BNE    : Reg -> Reg -> Lab -> Instruction
  SPIM_BGEZ   : Reg -> Lab        -> Instruction
  SPIM_BGTZ   : Reg -> Lab        -> Instruction
  SPIM_BLEZ   : Reg -> Lab        -> Instruction
  SPIM_BLTZ   : Reg -> Lab        -> Instruction
  SPIM_BLTZAL : Reg -> Lab        -> Instruction
  SPIM_BGEZAL : Reg -> Lab        -> Instruction
  SPIM_J      : Lab               -> Instruction
  SPIM_JAL    : Lab               -> Instruction
  SPIM_JR     : Reg               -> Instruction
  SPIM_JALR   : Reg               -> Instruction
  SPIM_LABEL  : Lab               -> Instruction

record ProcessorState where
  constructor MkPS
  instructionPtr : Nat
  instructions : List Instruction
  labels : SortedMap Lab Nat
  lo, hi : Bits32
  registers : Vect 32 Bits32
  memory : SortedMap Bits32 Bits32

SPIM : Type -> Type
SPIM t = State ProcessorState t

zeroAddr : Addr
zeroAddr = MkAddr 0

addOffset : Off -> Addr -> Addr
addOffset (MkOff o) (MkAddr a) = MkAddr (o + a)

setRegister : Reg -> Bits32 -> SPIM ()
setRegister k v = do
  s <- get
  put $ record { registers $= \r => (replaceAt (registerToFin k) v r) } s

getRegister : Reg -> SPIM Bits32
getRegister k = (index (registerToFin k) . registers) <$> get

getAddrFromRegister : Reg -> SPIM Addr
getAddrFromRegister r = pure (addOffset (MkOff !(getRegister r)) zeroAddr)

getMemory : Addr -> SPIM Bits32
getMemory (MkAddr a) = pure $ fromMaybe 0 $ lookup a !(memory <$> get)

setMemory : Addr -> Bits32 -> SPIM ()
setMemory (MkAddr a) v = get >>= (put . updateMem)
  where
    updateMem s = record { memory = insert a v (memory s) } s

getLabel : Lab -> SPIM Nat
getLabel = ?getLabel

shiftIP : Int -> SPIM ()
shiftIP i = put (record { instructionPtr $= updateIP } !(get))
  where
    updateIP ip = fromIntegerNat $ cast $ i + cast ip

getIP : SPIM Nat
getIP = instructionPtr <$> get

setIP : Nat -> SPIM ()
setIP n = put (record { instructionPtr = n } !(get))

jumpIP : Bits32 -> SPIM ()
jumpIP a = do
  setIP $ fromIntegerNat (cast (cast a))

getImm : Imm -> Bits32
getImm (MkImm i) = i

getLO : SPIM Bits32
getLO = pure (lo !get)

getHI : SPIM Bits32
getHI = pure (hi !get)

setLO : Bits32 -> SPIM ()
setLO i = put (record { lo = i } !get)

setHI : Bits32 -> SPIM ()
setHI i = put (record { hi = i } !get)

liftRSI : Reg -> Reg -> Imm -> (Bits32 -> Bits32 -> Bits32) -> SPIM ()
liftRSI r s (MkImm iv) f = setRegister r (f !(getRegister s) iv)

liftRST : Reg -> Reg -> Reg -> (Bits32 -> Bits32 -> Bits32) -> SPIM ()
liftRST r s t f = setRegister r (f !(getRegister s) !(getRegister t))

liftST : Reg -> Reg -> (Bits32 -> Bits32 -> SPIM ()) -> SPIM ()
liftST s t f = f !(getRegister s) !(getRegister t)

void : (Monad m) => m a -> m ()
void m = do { m; pure (); }

unless : (Monad m) => Bool -> m a -> m ()
unless False m = void m
unless True  _ = pure ()

when : (Monad m) => Bool -> m a -> m ()
when c = unless (not c)

Neg Bits32 where
    negate x = 0 - x
    x - y = prim__subB32 x y
    abs x = if x < 0 then -x else x

bitwiseAnd : Bits32 -> Bits32 -> Bits32
bitwiseAnd = prim__andB32

complement : Bits32 -> Bits32
complement = prim__complB32

bitwiseOr : Bits32 -> Bits32 -> Bits32
bitwiseOr = prim__orB32

bitwiseNor : Bits32 -> Bits32 -> Bits32
bitwiseNor x y = complement (bitwiseOr x y)

bitwiseXor : Bits32 -> Bits32 -> Bits32
bitwiseXor = prim__xorB32

shiftLeft : Bits32 -> Bits32 -> Bits32
shiftLeft = prim__shlB32

shiftRight : Bits32 -> Bits32 -> Bits32
shiftRight = prim__lshrB32

setLessThan : Bits32 -> Bits32 -> Bits32
setLessThan x y = if x < y then 1 else 0

step : Instruction -> SPIM ()
step (SPIM_ADD    r s t) = liftRST r s t (+)
step (SPIM_ADDU   r s t) = liftRST r s t (+)
step (SPIM_ADDI   r s i) = liftRSI r s i (+)
step (SPIM_SUB    r s t) = liftRST r s t (-)
step (SPIM_SUBU   r s t) = liftRST r s t (-)
step (SPIM_DIV    s t)   = liftST s t $ \sv, tv => do
                             unless (tv == 0) $ do
                               setLO (assert_total (div sv tv))
                               setHI (assert_total (mod sv tv))
step (SPIM_DIVU   s t)   = liftST s t $ \sv, tv => do
                             unless (tv == 0) $ do
                               setLO (assert_total (div sv tv))
                               setHI (assert_total (mod sv tv))
step (SPIM_MULT   s t)   = liftST s t $ \sv, tv => setLO (sv * tv)
step (SPIM_MULTU  s t)   = liftST s t $ \sv, tv => setLO (sv * tv)
step (SPIM_AND    r s t) = liftRST r s t bitwiseAnd
step (SPIM_ANDI   r s i) = liftRSI r s i bitwiseAnd
step (SPIM_NOR    r s t) = liftRST r s t bitwiseNor
step (SPIM_OR     r s t) = liftRST r s t bitwiseOr
step (SPIM_ORI    r s i) = liftRSI r s i bitwiseOr
step (SPIM_XOR    r s t) = liftRST r s t bitwiseXor
step (SPIM_XORI   r s i) = liftRSI r s i bitwiseXor
step (SPIM_SLL    r s i) = liftRSI r s i shiftLeft
step (SPIM_SLLV   r s t) = liftRST r s t shiftLeft
step (SPIM_SRL    r s i) = liftRSI r s i shiftRight
step (SPIM_SRLV   r s t) = liftRST r s t shiftRight
step (SPIM_MFLO   r)     = getLO >>= setRegister r
step (SPIM_MFHI   r)     = getHI >>= setRegister r
step (SPIM_LUI    r i)   = setRegister r (shiftLeft (getImm i) 16)
step (SPIM_LB     r o s) = ?step_lb
step (SPIM_LW     r o s) = setRegister r !(getMemory $ addOffset o !(getAddrFromRegister s))
step (SPIM_SB     r o s) = ?step_sb
step (SPIM_SW     r o s) = setMemory !(addOffset o <$> (getAddrFromRegister s)) !(getRegister r)
step (SPIM_SLT    r s t) = liftRST r s t setLessThan
step (SPIM_SLTU   r s t) = liftRST r s t setLessThan
step (SPIM_SLTI   r s i) = liftRSI r s i setLessThan
step (SPIM_BEQ    r s l) = ?step_beq
step (SPIM_BNE    r s l) = ?step_bne
step (SPIM_BGEZ   r l)   = ?step_bgez
step (SPIM_BGTZ   r l)   = ?step_bgtz
step (SPIM_BLEZ   r l)   = ?step_blez
step (SPIM_BLTZ   r l)   = ?step_bltz
step (SPIM_BLTZAL r l)   = ?step_bltzal
step (SPIM_BGEZAL r l)   = ?step_bgezal
step (SPIM_J      l)     = ?step_j
step (SPIM_JAL    l)     = ?step_jal
step (SPIM_JR     r)     = ?step_jr
step (SPIM_JALR   r)     = ?step_jalr
step (SPIM_LABEL  _)     = pure ()

-- run : [Instruction] -> SPIM ()
-- run (x:xs) = do step x
