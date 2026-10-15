import EncryptedMultitapeOutput

/-!
# Raw literal initializers on several tapes

Each initial tape cell is a constant or a fixed unary encoding of one raw
input bit. Constants may include length-dependent padding and rulers, but
the initializer cannot compute a function of multiple input bits.
-/

noncomputable section
namespace MultitapeLiteralInitialization
open TransformerAC0 ObliviousPhase MultitapeMatrix EncryptedMultitapeOutput

inductive SymbolSource (n : ℕ) (Symbol : Type*)
  | constant (symbol : Symbol)
  | bit (index : Fin n) (encode : Bool → Symbol)

namespace SymbolSource
variable {n : ℕ} {Symbol : Type*}

def eval (source : SymbolSource n Symbol) (input : Bits n) : Symbol :=
  match source with
  | .constant symbol => symbol
  | .bit index encode => encode (input index)

def predicateLiteral (source : SymbolSource n Symbol) (predicate : Symbol → Bool) :
    Autoregressive.ContextLiteral n :=
  match source with
  | .constant symbol => .constant (predicate symbol)
  | .bit index encode => EfficientMatrix.bitLiteral
      (predicate (encode false)) (predicate (encode true)) index

theorem predicateLiteral_correct (source : SymbolSource n Symbol)
    (predicate : Symbol → Bool) (input : Bits n) :
    (source.predicateLiteral predicate).eval input = predicate (source.eval input) := by
  cases source with
  | constant symbol => rfl
  | bit index encode =>
      rw [predicateLiteral, EfficientMatrix.eval_bitLiteral]
      cases h : input index <;> simp [eval, h]

end SymbolSource

variable {n tapes extra : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]

def initialTape (sources : Fin tapes → ℤ → SymbolSource n Symbol) (input : Bits n) :
    Fin tapes → ℤ → Symbol := fun tape cell => (sources tape cell).eval input

def tapeLiteral (blank : Symbol) (sources : Fin tapes → ℤ → SymbolSource n Symbol)
    (address : Fin tapes × RotationProgram.Address) (predicate : HeadMarker.Cell Symbol → Bool) :
    Autoregressive.ContextLiteral n :=
  match address.2 with
  | .inl cell => (sources address.1 cell).predicateLiteral
      (fun symbol => predicate (symbol, decide (cell = 0)))
  | .inr _ => .constant (predicate (blank, false))

omit [Fintype State] [Fintype Symbol] in
theorem tapeLiteral_correct (blank : Symbol) (sources : Fin tapes → ℤ → SymbolSource n Symbol)
    (address : Fin tapes × RotationProgram.Address) (predicate : HeadMarker.Cell Symbol → Bool)
    (input : Bits n) :
    (tapeLiteral blank sources address predicate).eval input =
      predicate (MultitapeEfficientPhase.initialMemory blank (initialTape sources input) address) := by
  obtain ⟨tape, address⟩ := address
  cases address with
  | inl cell => exact SymbolSource.predicateLiteral_correct _ _ input
  | inr cell => rfl

def finiteLiteral (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (blank : Symbol) (sources : Fin tapes → ℤ → SymbolSource n Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) :
    Fin ((eventCount machine anchor level extra + 2) * vocabulary tapes State Symbol) →
      Autoregressive.ContextLiteral n := fun wire =>
  let pair := finProdFinEquiv.symm wire
  Fin.cases (.constant (decide (pair.2 = ObliviousMatrix.tokenCode
      (.inl (MultitapeEfficientPhase.initialControl machine blank)))))
    (fun time => tapeLiteral blank sources
      ((MultitapeOutputMatrix.program machine anchor blank level outputTape cells).position time.val)
      (fun value => decide (pair.2 = ObliviousMatrix.tokenCode (.inr (.inl value))))) pair.1

theorem finiteLiteral_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (blank : Symbol) (sources : Fin tapes → ℤ → SymbolSource n Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ)
    (input : Bits n) (wire) :
    (finiteLiteral machine anchor blank sources level outputTape cells wire).eval input =
      RoutedMatrix.promptInput (ObliviousMatrix.prompt
        (MultitapeOutputMatrix.program machine anchor blank level outputTape cells)
        (eventCount machine anchor level extra) (initialTape sources input)) wire := by
  obtain ⟨⟨position, token⟩, rfl⟩ := finProdFinEquiv.surjective wire
  simp only [finiteLiteral, RoutedMatrix.promptInput, ObliviousMatrix.front, vocabulary,
    Equiv.symm_apply_apply]
  refine Fin.cases ?_ (fun time => ?_) position
  · simp only [ObliviousMatrix.prompt, ObliviousMatrix.front, vocabulary,
      Equiv.symm_apply_apply, Fin.cases_zero, Autoregressive.ContextLiteral.eval]
    rfl
  · simp only [Fin.cases_succ, tapeLiteral_correct, ObliviousMatrix.prompt,
      ObliviousMatrix.front, vocabulary, Equiv.symm_apply_apply]
    rfl

def binaryLiteral (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (blank : Symbol) (sources : Fin tapes → ℤ → SymbolSource n Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) :=
  BinaryMatrix.promptLiteral (finiteLiteral machine anchor blank sources level outputTape cells)

theorem binaryLiteral_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (blank : Symbol) (sources : Fin tapes → ℤ → SymbolSource n Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ)
    (input : Bits n) (wire) :
    (binaryLiteral machine anchor blank sources level outputTape cells wire).eval input =
      RoutedMatrix.promptInput (plainPrompt machine anchor blank level outputTape cells
        (initialTape sources input)) wire :=
  BinaryMatrix.promptLiteral_correct _ input _
    (finiteLiteral_correct machine anchor blank sources level outputTape cells input) wire

end MultitapeLiteralInitialization
