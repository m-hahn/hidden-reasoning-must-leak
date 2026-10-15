import ExactEncryptedAlphabet
import TaskReductions

/-! # The paper's exact task vocabularies, with shared bit/output symbols -/

noncomputable section
namespace ExactTaskAlphabet
open TransformerAC0 TaskReductions

def boolCode : Option Bool ≃ Fin (Fintype.card (Option Bool)) := Fintype.equivFin _
def binaryBit (bit : Bool) : Fin 3 := (BinarySchedule.bitToken bit).castSucc
def binaryOutput (value : Fin (Fintype.card (Option Bool))) : Fin 3 :=
  match boolCode.symm value with
  | none => Fin.last 2
  | some bit => binaryBit bit
def binaryAlphabet : ExactEncryptedAlphabet.Alphabet 3 (Fintype.card (Option Bool)) where
  bit := binaryBit
  readBit token := decide (token = 1)
  readBit_bit bit := by cases bit <;> simp [binaryBit, BinarySchedule.bitToken]
  output := binaryOutput

@[simp] theorem binaryOutput_some (bit : Bool) : binaryOutput (boolCode (some bit)) = binaryBit bit := by
  simp [binaryOutput]
@[simp] theorem binaryOutput_none : binaryOutput (boolCode none) = Fin.last 2 := by simp [binaryOutput]

def decodeBinaryToken : Fin 4 → Option Bool :=
  Fin.lastCases none (Fin.lastCases none (fun token : Fin 2 => some (BinarySchedule.tokenBit token)))

@[simp] theorem decodeBinaryToken_output (value : Option Bool) :
    decodeBinaryToken (ProtocolMatrix.dataToken (binaryOutput (boolCode value))) = value := by
  cases value with
  | none =>
      rw [binaryOutput_none]
      change Fin.lastCases none (Fin.lastCases none (fun token : Fin 2 => some (BinarySchedule.tokenBit token))) (Fin.last 2).castSucc = none
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  | some bit => simp [decodeBinaryToken, ProtocolMatrix.dataToken, binaryBit]

def groupEnumeration : Fintype S5 := Fintype.ofFinite S5
local instance : Fintype S5 := groupEnumeration
def groupCode : S5 ≃ Fin (Fintype.card S5) := Fintype.equivFin _
def groupOptionCode : Option S5 ≃ Fin (Fintype.card (Option S5)) := Fintype.equivFin _
def groupBit (bit : Bool) : Fin (Fintype.card S5 + 1) := (groupCode (s5Encode bit)).castSucc
def groupReadBit : Fin (Fintype.card S5 + 1) → Bool :=
  Fin.lastCases false (fun value => oddUnit (Equiv.Perm.sign (groupCode.symm value)))
def groupOutput (value : Fin (Fintype.card (Option S5))) : Fin (Fintype.card S5 + 1) :=
  match groupOptionCode.symm value with
  | none => Fin.last (Fintype.card S5)
  | some permutation => (groupCode permutation).castSucc
def groupAlphabet : ExactEncryptedAlphabet.Alphabet (Fintype.card S5 + 1) (Fintype.card (Option S5)) where
  bit := groupBit
  readBit := groupReadBit
  readBit_bit bit := by simp [groupReadBit, groupBit]
  output := groupOutput

@[simp] theorem groupOutput_some (permutation : S5) :
    groupOutput (groupOptionCode (some permutation)) = (groupCode permutation).castSucc := by simp [groupOutput]
@[simp] theorem groupOutput_none : groupOutput (groupOptionCode none) = Fin.last (Fintype.card S5) := by simp [groupOutput]

def additionBit (bit : Bool) : Fin 102 := if bit then ⟨1, by omega⟩ else ⟨0, by omega⟩
def additionOutput (value : Fin (Fintype.card (Option Bool))) : Fin 102 :=
  match boolCode.symm value with
  | none => Fin.last 101
  | some bit => additionBit bit
def additionAlphabet : ExactEncryptedAlphabet.Alphabet 102 (Fintype.card (Option Bool)) where
  bit := additionBit
  readBit token := decide (token = 1)
  readBit_bit bit := by cases bit <;> simp [additionBit]
  output := additionOutput

@[simp] theorem additionOutput_some (bit : Bool) : additionOutput (boolCode (some bit)) = additionBit bit := by simp [additionOutput]
@[simp] theorem additionOutput_none : additionOutput (boolCode none) = Fin.last 101 := by simp [additionOutput]

theorem s5_vocabulary_card : Fintype.card S5 + 1 + 1 = 122 := by
  have h : Fintype.card S5 = 120 := by
    have hcard := Fintype.card_perm (α := Fin 5)
    have he := @Fintype.card_congr S5 (Equiv.Perm (Fin 5)) groupEnumeration (Equiv.instFintype) (Equiv.refl _)
    exact he.trans (by simpa using hcard)
  omega

end ExactTaskAlphabet
