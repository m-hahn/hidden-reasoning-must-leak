import ProtocolMultitapeMatrix
import SeedBudget
import PRGRestriction
import PRGReindex
import ProtocolSerialization

/-!
# Derived sublinear-seed privacy for actual polynomial-time computation

The full PRG stretch is restricted to the exact binary event payload by a
proved free-wiring reduction. Seed size and sufficient pad capacity are
derived from the source time exponent, not given as simulation certificates.
The only cryptographic premise is security of the specified NC⁰ family.
-/

noncomputable section
namespace PrivatePolynomialTime
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix
variable {tapes : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]

def payloadCoefficient (tapes : ℕ) (State Symbol : Type*) [Fintype State] [Fintype Symbol]
    (coefficient exponent : ℕ) : ℕ :=
  polynomialTraceConstant tapes coefficient exponent * vocabulary tapes State Symbol + 1

def seedLengths (tapes : ℕ) (State Symbol : Type*) [Fintype State] [Fintype Symbol]
    (coefficient exponent : ℕ) (stretch : ℝ) : ℕ → ℕ :=
  SeedBudget.length exponent stretch (payloadCoefficient tapes State Symbol coefficient exponent)

def stretchLengths (tapes : ℕ) (State Symbol : Type*) [Fintype State] [Fintype Symbol]
    (coefficient exponent : ℕ) (stretch : ℝ) : ℕ → ℕ :=
  fun n => ⌊(seedLengths tapes State Symbol coefficient exponent stretch n : ℝ) ^ stretch⌋₊

/-- The research import is the ordinary family indexed by its seed length,
not a stronger security assumption about the simulation's chosen lengths. -/
abbrev SeedIndexedGenerator (stretch : ℝ) :=
  NC0GeneratorFamily id (fun seed => ⌊(seed : ℝ) ^ stretch⌋₊)

def chosenGenerator (coefficient exponent : ℕ) (stretch : ℝ)
    (generator : SeedIndexedGenerator stretch) :
    NC0GeneratorFamily (seedLengths tapes State Symbol coefficient exponent stretch)
      (stretchLengths tapes State Symbol coefficient exponent stretch) :=
  PRGReindex.family generator (seedLengths tapes State Symbol coefficient exponent stretch)

theorem chosenGenerator_secure (coefficient exponent : ℕ) (hexponent : 1 ≤ exponent)
    (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
    (generator : SeedIndexedGenerator stretch) (security : generator.IsPseudorandom) :
    (chosenGenerator (tapes := tapes) (State := State) (Symbol := Symbol)
      coefficient exponent stretch generator).IsPseudorandom := by
  obtain ⟨degree, _, hinverse⟩ := SeedBudget.seed_inverse_bound
    (size := (payloadCoefficient tapes State Symbol coefficient exponent : ℝ))
    (by exact_mod_cast (show 0 < exponent by omega)) hstretch
  apply PRGReindex.secure generator security _ degree
  intro n
  exact (hinverse n).trans (Nat.pow_le_pow_left (Nat.le_succ _) degree)

theorem payload_bound (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (time n coefficient exponent : ℕ) (bound : time ≤ coefficient * (n + 1) ^ exponent) :
    eventSteps machine anchor (horizonLevel (max 1 time)) * vocabulary tapes State Symbol + 1 ≤
      payloadCoefficient tapes State Symbol coefficient exponent * (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) := by
  have h := Nat.mul_le_mul_right (vocabulary tapes State Symbol)
    (polynomial_log_trace_bound machine anchor time n coefficient exponent bound)
  have hp : 1 ≤ (n + 1) ^ exponent := Nat.one_le_pow _ _ (by omega)
  have hq : 1 ≤ (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) := by nlinarith
  calc
    _ ≤ (polynomialTraceConstant tapes coefficient exponent * (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1)) *
        vocabulary tapes State Symbol + (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) := Nat.add_le_add h hq
    _ = _ := by unfold payloadCoefficient; ring

theorem capacity (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (time n coefficient exponent : ℕ) (bound : time ≤ coefficient * (n + 1) ^ exponent)
    (hexponent : 1 ≤ exponent) (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch) :
    eventSteps machine anchor (horizonLevel (max 1 time)) * vocabulary tapes State Symbol + 1 ≤
      stretchLengths tapes State Symbol coefficient exponent stretch n := by
  apply SeedBudget.stretch_floor_capacity (k := (exponent : ℝ)) (size := (payloadCoefficient tapes State Symbol coefficient exponent : ℝ))
    (by exact_mod_cast hexponent) hstretch (by positivity)
  have h := payload_bound machine anchor time n coefficient exponent bound
  simp only [Real.rpow_natCast]
  exact_mod_cast h

def generatorPrefix {times : ℕ → ℕ}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (coefficient exponent : ℕ)
    (time_bound : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent) (hexponent : 1 ≤ exponent)
    (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
    (generator : NC0GeneratorFamily (seedLengths tapes State Symbol coefficient exponent stretch)
      (stretchLengths tapes State Symbol coefficient exponent stretch)) :
    NC0GeneratorFamily (seedLengths tapes State Symbol coefficient exponent stretch)
      (fun n => eventSteps machine anchor (horizonLevel (max 1 (times n))) * vocabulary tapes State Symbol + 1) :=
  PRGRestriction.family generator (fun n => capacity machine anchor (times n) n coefficient exponent (time_bound n) hexponent stretch hstretch)

theorem generatorPrefix_secure {times : ℕ → ℕ}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (coefficient exponent : ℕ)
    (time_bound : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent) (hexponent : 1 ≤ exponent)
    (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
    (generator : NC0GeneratorFamily (seedLengths tapes State Symbol coefficient exponent stretch)
      (stretchLengths tapes State Symbol coefficient exponent stretch)) (secure : generator.IsPseudorandom) :
    (generatorPrefix machine anchor coefficient exponent time_bound hexponent stretch hstretch generator).IsPseudorandom :=
  PRGRestriction.secure generator secure _

/-- The whole native Boolean-output model, using the derived seed length
and a prefix of the seed-indexed PRG. Construction needs no security premise;
security is used only in the privacy theorem. -/
def model {times : ℕ → ℕ}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape outputTape : Fin tapes) (cells : ℕ → ℤ) (decode : Symbol → Bool)
    (coefficient exponent : ℕ) (time_bound : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent)
    (hexponent : 1 ≤ exponent) (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
    (generator : SeedIndexedGenerator stretch) (n : ℕ) :=
  ProtocolMultitapeMatrix.model machine anchor blank bitSymbol inputTape n (horizonLevel (max 1 (times n)))
    outputTape (cells n) decode
    ((generatorPrefix machine anchor coefficient exponent time_bound hexponent stretch hstretch
      (chosenGenerator coefficient exponent stretch generator)).generator n)

theorem output_at_source_time {times : ℕ → ℕ}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape outputTape : Fin tapes) (cells : ℕ → ℤ) (decode : Symbol → Bool)
    (coefficient exponent : ℕ) (time_bound : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent)
    (hexponent : 1 ≤ exponent) (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
    (generator : SeedIndexedGenerator stretch) (n : ℕ) (input : Bits n)
    (seed : Bits (seedLengths tapes State Symbol coefficient exponent stretch n))
    (terminal : ∀ symbols, machine.transition
      (machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine (bitTape blank bitSymbol inputTape input))).state symbols =
      ((machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine (bitTape blank bitSymbol inputTape input))).state,
        symbols, fun _ => Direction.stay)) :
    (model machine anchor blank bitSymbol inputTape outputTape cells decode coefficient exponent time_bound
      hexponent stretch hstretch generator n).answer
      (ProtocolMultitapeMatrix.inputEncoding machine anchor blank bitSymbol inputTape (horizonLevel (max 1 (times n)))
        outputTape (cells n) input seed) =
      decode ((machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine
        (bitTape blank bitSymbol inputTape input))).tape outputTape (cells n)) := by
  unfold model
  rw [ProtocolMultitapeMatrix.output_correct]
  rw [machine.terminal_run_after _ (times n) _
    ((Nat.le_max_right 1 (times n)).trans (horizon_covers (max 1 (times n)))) terminal]

theorem context_bound {times : ℕ → ℕ}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape outputTape : Fin tapes) (cells : ℕ → ℤ) (decode : Symbol → Bool)
    (coefficient exponent : ℕ) (time_bound : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent)
    (hexponent : 1 ≤ exponent) (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
    (generator : SeedIndexedGenerator stretch) (n : ℕ) :
    (model machine anchor blank bitSymbol inputTape outputTape cells decode coefficient exponent time_bound
      hexponent stretch hstretch generator n).architecture.contextLength ≤
      (⌈SeedBudget.coefficient exponent stretch (payloadCoefficient tapes State Symbol coefficient exponent)⌉₊ +
        2 * payloadCoefficient tapes State Symbol coefficient exponent + 2 * vocabulary tapes State Symbol + 1) *
      (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) := by
  unfold model
  rw [ProtocolMultitapeMatrix.context_length]
  have hseed := SeedBudget.seed_polynomial_bound
    (size := (payloadCoefficient tapes State Symbol coefficient exponent : ℝ))
    (by exact_mod_cast (show 0 < exponent by omega)) hstretch n
  have htrace := payload_bound machine anchor (times n) n coefficient exponent (time_bound n)
  have hp : n + 1 ≤ (n + 1) ^ exponent := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < n + 1) hexponent
  have hscale : n + 1 ≤ (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) := by nlinarith
  have hseed' := hseed.trans (Nat.mul_le_mul_left
    ⌈SeedBudget.coefficient exponent stretch (payloadCoefficient tapes State Symbol coefficient exponent)⌉₊ hscale)
  change seedLengths tapes State Symbol coefficient exponent stretch n ≤ _ at hseed'
  nlinarith

/-- The actual binary encrypted matrix trace satisfies arbitrary-prior,
arbitrary-predicate privacy with the derived sublinear seed allocation.
There is no supplied pad-capacity or circuit/matrix-realization premise. -/
theorem no_readability {times : ℕ → ℕ}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape outputTape : Fin tapes) (cells : ℕ → ℤ) (decode : Symbol → Bool)
    (coefficient exponent : ℕ) (time_bound : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent)
    (hexponent : 1 ≤ exponent) (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
    (generator : SeedIndexedGenerator stretch) (secure : generator.IsPseudorandom)
    (monitor : PolynomialMonitorFamily
      (fun n => eventSteps machine anchor (horizonLevel (max 1 (times n))) * vocabulary tapes State Symbol)) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Bits n)) (predicate : Bits n → Bool),
      predictionSuccess distribution
        (fun input seed => ProtocolMultitapeMatrix.transcript machine anchor blank bitSymbol inputTape
          (horizonLevel (max 1 (times n))) outputTape (cells n) decode
          ((generatorPrefix machine anchor coefficient exponent time_bound hexponent stretch hstretch
            (chosenGenerator coefficient exponent stretch generator)).generator n)
          input seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n :=
  ProtocolMultitapeMatrix.no_readability machine anchor blank bitSymbol inputTape outputTape cells decode _
    (generatorPrefix_secure machine anchor coefficient exponent time_bound hexponent stretch hstretch
      (chosenGenerator coefficient exponent stretch generator)
      (chosenGenerator_secure coefficient exponent hexponent stretch hstretch generator secure))
    monitor coefficient exponent time_bound

/-- An observer may inspect any fixed encoding of every actual generated
payload token and the separator, not just the extracted ciphertext bits. -/
theorem no_readability_full_word {times : ℕ → ℕ} {codeWidth : ℕ}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape outputTape : Fin tapes) (cells : ℕ → ℤ) (decode : Symbol → Bool)
    (coefficient exponent : ℕ) (time_bound : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent)
    (hexponent : 1 ≤ exponent) (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
    (generator : SeedIndexedGenerator stretch) (secure : generator.IsPseudorandom)
    (encoding : ProtocolSerialization.Encoding codeWidth)
    (monitor : PolynomialMonitorFamily
      (fun n => (eventSteps machine anchor (horizonLevel (max 1 (times n))) * vocabulary tapes State Symbol + 1) * codeWidth)) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Bits n)) (predicate : Bits n → Bool),
      predictionSuccess distribution
        (fun input seed => ProtocolSerialization.transcript
          (ProtocolMultitapeMatrix.schedule machine anchor blank bitSymbol inputTape n
            (horizonLevel (max 1 (times n))) outputTape (cells n))
          (ProtocolMultitapeMatrix.transition machine blank outputTape decode) BinarySchedule.tokenBit
          ((generatorPrefix machine anchor coefficient exponent time_bound hexponent stretch hstretch
            (chosenGenerator coefficient exponent stretch generator)).generator n) encoding
          (ProtocolMultitapeMatrix.plainPrompt machine anchor blank bitSymbol inputTape
            (horizonLevel (max 1 (times n))) outputTape (cells n) input) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n :=
  ProtocolSerialization.no_readability
    (fun n => ProtocolMultitapeMatrix.schedule machine anchor blank bitSymbol inputTape n
      (horizonLevel (max 1 (times n))) outputTape (cells n))
    (ProtocolMultitapeMatrix.transition machine blank outputTape decode) BinarySchedule.tokenBit
    (fun n input => ProtocolMultitapeMatrix.plainPrompt machine anchor blank bitSymbol inputTape
      (horizonLevel (max 1 (times n))) outputTape (cells n) input)
    (generatorPrefix machine anchor coefficient exponent time_bound hexponent stretch hstretch
      (chosenGenerator coefficient exponent stretch generator))
    (generatorPrefix_secure machine anchor coefficient exponent time_bound hexponent stretch hstretch
      (chosenGenerator coefficient exponent stretch generator)
      (chosenGenerator_secure coefficient exponent hexponent stretch hstretch generator secure))
    encoding monitor
    (((4 * (248 * tapes + 1)) * (coefficient + 2) ^ 2) * vocabulary tapes State Symbol) (2 * exponent)
    (fun n => ProtocolMultitapeMatrix.payload_polynomial_bound machine anchor (times n) n coefficient exponent (time_bound n))

/-- The exponent c is selected between the source exponent and stretch;
the seed is bounded by a sublinear power and is polynomially bounded. -/
theorem seed_resource_bounds (coefficient exponent : ℕ) (hexponent : 1 ≤ exponent) (stretch : ℝ)
    (hstretch : (exponent : ℝ) < stretch) :
    ∃ c : ℝ, (exponent : ℝ) < c ∧ c < stretch ∧ 0 < (exponent : ℝ) / c ∧ (exponent : ℝ) / c < 1 ∧
      ∀ n : ℕ,
        (seedLengths tapes State Symbol coefficient exponent stretch n : ℝ) ≤
          (SeedBudget.coefficient exponent stretch (payloadCoefficient tapes State Symbol coefficient exponent) + 1) *
            (n + 1 : ℝ) ^ ((exponent : ℝ) / c) := by
  obtain ⟨c, hlow, hhigh, hpositive, hsublinear, hbound, _⟩ :=
    SeedBudget.sublinear_seed_and_capacity (k := (exponent : ℝ))
      (size := (payloadCoefficient tapes State Symbol coefficient exponent : ℝ))
      (by exact_mod_cast hexponent) hstretch (by positivity)
  exact ⟨c, hlow, hhigh, hpositive, hsublinear, hbound⟩

end PrivatePolynomialTime
