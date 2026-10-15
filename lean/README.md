# Lean verification of the theoretical appendix

This directory contains the Lean verification for
[Hidden Reasoning Must Leak, but Need Not Be Readable: Fundamental Opportunities and Limits for Chain-of-Thought Monitoring](https://arxiv.org/abs/2609.37312)
(arXiv:2609.37312).

The project-specific formalization, adaptations, and integration were produced
by GPT-6.1-Sol with input from Michael Hahn. This attribution does not claim
authorship of the third-party proofs and infrastructure credited below.

## License

The Lean verification's original project code, scripts, and accompanying
documentation are released under the [MIT License](LICENSE), copyright
2026 Michael Hahn and contributors. This includes our own additions and
modifications, to the extent that we hold rights in them.

Third-party code retains its own licenses and notices. In particular, the
MIT and Apache-2.0 files identified below and in [NOTICE](NOTICE) and
[third_party_manifest.json](third_party_manifest.json) are not relicensed
by the project's MIT license. When a file contains both upstream material
and our modifications, the MIT grant for our contributions does not remove
the upstream license requirements. Keep all applicable licenses and notices
when redistributing the combined development.

## Third-party code and acknowledgments

This development builds on substantial work by other authors. In particular,
the switching-lemma and classical multiplication libraries supply mathematical
proofs, not merely utilities. We gratefully acknowledge their original authors
and the Lean, mathlib, and CSLib communities. Copying, porting, adapting, or
checking these sources locally does not make them original work of this project.

| Included code | Original work and contribution | Preserved license |
| --- | --- | --- |
| [Complexitylib/Algebraic/](Complexitylib/Algebraic/) | Samuel Schlesinger's [complexitylib](https://github.com/SamuelSchlesinger/complexitylib/tree/add0aca8ee0d71e68969f2cb45cf91554a50f787): single-formula switching proofs, canonical encodings, advice counts, decision trees, and restriction infrastructure. | [MIT, copyright 2026 Samuel Schlesinger](Complexitylib/Algebraic/LICENSE) |
| [Complexitylib/Cslib/](Complexitylib/Cslib/) | Samuel Schlesinger's circuit wiring extensions from the same complexitylib revision. | [Apache-2.0](Complexitylib/LICENSE) |
| [Cslib/](Cslib/) | [leanprover/cslib](https://github.com/leanprover/cslib/tree/311d27ad8458b61e9b7461fc83a480e4be97aef2): circuit foundations by Samuel Schlesinger, and initialization adapted from Jesse Alama's work. We also acknowledge the wider CSLib contributor community. | [Apache-2.0](Cslib/LICENSE); original per-file author/copyright notices retained |
| [IntegerMultBounds/](IntegerMultBounds/) | Kenny Daniel's [integer-mult-bounds-lean](https://github.com/platypii/integer-mult-bounds-lean/tree/9b148a008183b1342e134af1270d3a7dafad4a9c): the classical Schönhage–Strassen proof dependency subtree, including arithmetic, machine routines, correctness, and cost proofs. | [MIT, copyright 2026 Kenny Daniel](IntegerMultBounds/LICENSE) |

[TalBlockAdvice.lean](TalBlockAdvice.lean) also adapts Samuel Schlesinger's
MIT-licensed binomial/exponential counting proof outside the vendored folders;
its source header explicitly credits that contribution. Our full Tal proof
uses the upstream single-formula switching development, and our multiplication
construction uses Kenny Daniel's classical multiplier proofs. Neither is
presented as having been formalized wholly from scratch here.

[NOTICE](NOTICE) records authorship, pinned revisions, modifications, license
locations, dependency credits, and redistribution instructions.
[third_party_manifest.json](third_party_manifest.json) identifies every
vendored or directly adapted Lean source file and its exact upstream source.
The full license texts are included unchanged; these acknowledgments supplement,
not replace, them. The pinned upstream snapshots have no separate `NOTICE`
files; this project's `NOTICE` is an additional attribution record, not a
fabricated upstream notice. The standard external packages in
[lake-manifest.json](lake-manifest.json), including mathlib and its dependencies,
remain credited to their own contributors and retain their own licenses.

Run `ruby scripts/check_third_party.rb` from this directory to check the
recorded file inventory, source notices, license texts, and dependency pins.
Run `ruby scripts/test_check_third_party.rb` for read-only regression tests
that ensure omitted credits, changed licenses, and inventory/pin drift fail.
See `NOTICE` before redistributing sources, compiled artifacts, or dependency
caches. The project-specific authorship statement above does not relicense
third-party material or imply endorsement by upstream authors.

## Scope of the verification

This directory develops the paper's lower bounds, entropy consequences, task
reductions, finite-precision compilation, and encryption reductions. Tal's
full Fourier-tail theorem is now proved locally, with its original `216^d`
bound. The only remaining research-level premise for the current
`N * polylog(N)` encrypted results is a secure ordinary seed-indexed NC⁰ PRG.
Multiplication is supplied by locally checked Schönhage–Strassen proofs,
not an external multiplication-complexity premise.
The general encrypted string-output construction now includes empty and
input-dependent-length answers terminated by a native EOS. Its output
capacity, seed budget, PRG prefix capacity, security reindexing, fixed
precision, constant heads, raw-input initialization, and polynomial matrix
resources are derived. The context bound is `O(N^k log N)`.
Direct linear-time models compute parity, the entire `S₅` product, and
addition on `{1,…,100}`; their encrypted versions emit the complete result
and EOS. A fixed classical multiplication machine now yields native encrypted
reasoning, the middle product bit, and EOS with `O(N log³ N)` context and a
sublinear seed for every permitted stretch exponent greater than one.
Privacy covers any fixed encoding of every actual reasoning token and its
separator, with arbitrary input priors and predicates on full finite input
alphabets. The plaintext output suffix is excluded from that prefix.

The native constructors now use the exact task vocabularies: four symbols
for parity and multiplication, all 120 `S₅` symbols plus EOS/separator, and
103 symbols for positive addition (the 100 input values plus 0, EOS, and
separator; 1 is shared). Public source positions recover bit roles through
fixed finite opcodes, so seed, plaintext, ciphertext, and output roles do
not require additional visible packet symbols. This is a new numerical
matrix constructor whose native greedy tokens are proved correct.

`ExactTasks.elementary_tasks_complete` assembles native complete outputs/EOS,
linear context, fixed heads/precision, polynomial resources, sublinear seed,
arbitrary-prior computational privacy, and seeded information/expected-length
bounds for the same parity, full-`S₅`, and positive-addition models.
`VerifiedMultiplication.complete` assembles the corresponding four-token
multiplication model, with `O(N log³ N)` context for every stretch greater
than one, using Tal and a multiplication algorithm proved locally. Its only
research premise is the secure NC⁰ generator.
`PlainBinaryWord.whole_function_correct` gives unconditional whole-word
Turing simulation with no seed or PRG premise. Its four-token matrices have
one layer, fixed heads/precision, polynomial resources, and
`O(N^k log N)` context. `ExactBinaryWord.whole_function_correct` computes
entire binary output words with encrypted reasoning,
including empty and input-dependent-length answers, in the four-token
alphabet from an ordinary polynomial-time source machine. Its source time
derives the output capacity; the raw initializer and all simulation,
resource, and cryptographic reductions are checked locally.
`PlainTasks.lean` supplies seed-free native parity, full-`S₅`, and
positive-addition outputs/EOS in those same exact alphabets, with linear
context and polynomial resources. `VerifiedPlainMultiplication.complete`
supplies the seed-free four-token multiplication construction with no
research premise, including no Tal, PRG, or multiplication assumption.
The older `ExactMultiplication.complete` and `PlainMultiplication.complete`
interfaces retain the sharper `O(N log² N)` context bound conditional on the
old `N log N` machine premise; they are optional, not needed for the accepted
`N * polylog(N)` scope.

## Paper-to-Lean theorem map

The numbering below is that of [arXiv:2609.37312v1](https://arxiv.org/abs/2609.37312v1).
It covers every numbered theorem, lemma, corollary, and proposition in the
main paper and appendices A and B. Appendices C--F contain experiments and
discussion, not additional numbered mathematical results to map here.
The local paper sources are [paper.tex](../ARXIV/paper.tex) and
[ARXIV_theoretical_details.tex](../ARXIV/ARXIV_theoretical_details.tex).

Each linked identifier is a Lean declaration, not just a suggested module.
A paper result can correspond to several declarations: the development
usually states explicit finite inequalities and separates correctness,
resources, information, and security, rather than copying an asymptotic
display into a single proposition. The coverage column records these
differences and distinguishes proved components from a complete matrix
construction. Any `tal` argument on an older helper can be filled by
[TalComplete.fourierTailTheorem](TalComplete.lean); it is no longer an
external research premise.

### Main results and their appendix restatements

| Paper result | Lean theorem(s) | Coverage and qualifications |
| --- | --- | --- |
| Theorem 3.1 / Theorem B.8: computation footprint | [TokenAutoregressive.Generator.footprint](TokenAutoregressive.lean); [TokenSymbolic.Generator.uniform_footprint](TokenSymbolic.lean); [ConcreteReasoning.token_multiplication_footprint](ConcreteReasoning.lean) | Explicit mutual-information lower bounds for actual full-vocabulary, separator-terminated matrix traces. The symbolic theorem covers the paired alphabets for S₅ and addition; multiplication has its own Fourier rate. [Footprint.footprint_tradeoff_of_sign_correlation](Footprint.lean) supplies the algebraic tradeoff rearrangement under its stated correlation hypothesis. These are finite counterparts, not one declaration using the paper's task-set and `Ω̃` notation. |
| Corollary 3.2 / Corollary B.9: correlated-public length tax | [ConcreteReasoning.hidden_reasoning_tax](ConcreteReasoning.lean); [ConcreteReasoning.token_hidden_reasoning_tax](ConcreteReasoning.lean) | The general finite entropy/source-coding inequality includes the public marginal, an actual public decoder, and the mutual-information subtraction. The second theorem composes it with a parity matrix computation. The aligned computation upper-bound components are [PlainTasks.context_linear](PlainTasks.lean) and [VerifiedPlainMultiplication.complete](VerifiedPlainMultiplication.lean); there is no single declaration assembling every task and both sides of this corollary. |
| Theorem 3.3 / Theorem B.11: private randomness and leakage | [FiniteInformation.Distribution.private_randomness_information_lower_bound](FiniteInformation.lean); [TokenAutoregressive.Generator.seeded_footprint](SeededToken.lean); [TokenAutoregressive.Generator.seeded_expected_length_lower_bound](SeededToken.lean); [TokenAutoregressive.Generator.seeded_multiplication_footprint](SeededToken.lean); [TokenAutoregressive.Generator.seeded_multiplication_expected_length_lower_bound](SeededToken.lean) | The general finite-distribution lemma proves the seed-entropy loss. The matrix corollaries give the `-r` information bound and the seed-independent expected-length bound for parity and multiplication. [ExactFoldTrace.information_lower_bound](ExactFoldTrace.lean) and [ExactFoldTrace.expected_length_lower_bound](ExactFoldTrace.lean) apply the same argument to the constructed full-alphabet elementary tasks. No PRG security is needed for these lower bounds. |
| Theorem 3.5 / Theorem B.14: encrypted task computation | [ExactTasks.elementary_tasks_complete](ExactFoldTheorem.lean); [VerifiedMultiplication.complete](VerifiedMultiplication.lean) | Complete same-model statements: output/EOS, fixed heads and precision, polynomial matrix resources, sublinear seeds, arbitrary-prior predicate privacy, and information/expected-length bounds. The elementary cases have linear context; multiplication has `O(N log³ N)` context. The sole research premise is the ordinary secure NC⁰ generator. Seed lengths are explicit integer budgets bounded by a sublinear power, not literal equalities to the idealized power displayed in the paper. |

### Additional appendix lemmas and theorems

| Paper result | Lean theorem(s) | Coverage and qualifications |
| --- | --- | --- |
| Lemma B.3: fixed-precision Transformer to AC⁰ | [TransformerAC0.fpt_to_ac0](TransformerAC0.lean); [CanonicalArithmetic.matrix_transformer_to_ac0](CanonicalArithmetic.lean) | Exact circuit evaluation, depth linear in nonzero layer count, and polynomial size in parameter count plus context length. The latter theorem specializes to the locally defined rounded numerical arithmetic. No circuit-realization certificate is assumed. |
| Theorem B.4: Tal's Fourier tail | [TalComplete.fourierTailTheorem](TalComplete.lean); [TalConsequences.parityCorrelation_sq_le](TalConsequences.lean); [TalConsequences.circuit_correlation_le](TalConsequences.lean) | Full general tail theorem with the original `216^d` constant, and its parity/general-correlation consequences. Proved locally for the original shared-circuit DSL; no Tal or switching assumption. |
| Lemma B.5: parity information bound | [Footprint.ParityTrace.transcriptProbability_le_of_correlation](Footprint.lean); [Footprint.footprint_from_tal](Footprint.lean); [TokenAutoregressive.Generator.footprint](TokenAutoregressive.lean) | Fiber-probability cap, finite Shannon information inequality, and composition with actual variable-length matrix execution. The first is the generic correlation-to-fiber step; the last derives the circuit family rather than requiring one. |
| Corollary B.6: S₅, addition, and multiplication reductions | [TokenSymbolic.Generator.uniform_footprint](TokenSymbolic.lean); [TokenSymbolic.s5_uniform_expected_length](TokenSymbolic.lean); [TokenSymbolic.positive_addition100_uniform_expected_length](PositiveAdditionFootprint.lean); [ConcreteReasoning.token_multiplication_footprint](ConcreteReasoning.lean); [ConcreteReasoning.token_multiplication_expected_length](ConcreteReasoning.lean) | Full-uniform symbolic input alphabets, not just a two-symbol restriction. Use [TaskReductions.s5Pairing](TaskReductions.lean) or [TaskReductions.positiveAdditionPairing100](PositiveAdditionFootprint.lean) in the generic symbolic information theorem. The positive-addition convention is exactly `{1,…,100}`. |
| Lemma B.15: unencrypted multitape simulation | [PlainBinaryWord.whole_function_correct](PlainBinaryWord.lean); [PlainBinaryWord.architecture_fixed](PlainBinaryWord.lean); [PlainBinaryWord.context_bound](PlainBinaryWord.lean); [PlainBinaryWord.polynomial_resources](PlainBinaryWord.lean) | Ordinary source-machine correctness is compiled to whole binary output words and first EOS, including empty and input-dependent-length outputs. One layer, four tokens, fixed heads/precision, and explicit `O(N^k log N)` context for a polynomial source-time bound. No seed or PRG premise. |
| Theorem B.16: encrypted polynomial-time computation | [ExactBinaryWord.whole_function_correct](ExactBinaryWord.lean); [ExactBinaryWord.architecture_fixed](ExactBinaryWord.lean); [ExactBinaryWord.context_bound](ExactBinaryWord.lean); [ExactBinaryWord.polynomial_resources](ExactBinaryWord.lean); [ExactBinaryWord.no_readability](ExactBinaryWord.lean); [PrivatePolynomialTime.seed_resource_bounds](PrivatePolynomialTime.lean) | The same whole-output compilation with encrypted reasoning, context/resources, and arbitrary-prior predicate privacy. Generator stretch must exceed the source-time exponent. Output correctness does not require security; privacy does. The seed theorem gives the explicit sublinear-power bound with an intermediate exponent. |
| Theorem B.17: low-degree mass of the middle multiplication bit | [ElementaryMultiplication.middle_bit_lowDegreeWeight_bound](ElementaryMultiplication.lean); [ElementaryMultiplication.middle_bit_fourier_resilience](ElementaryMultiplication.lean); [MultiplicationFootprint.lowerWeight_middleBit_eq](MultiplicationFootprint.lean) | The finite bound is `W_{≤N/8} ≤ 9 N² (4/5)^N` for every `N ≥ 2`. Exponential decay is stated with `Filter.atTop` (all sufficiently large `N`); the Boolean-cube theorem identifies the residue-pair and bit-coordinate definitions. This is not a literal formalization of the paper's fixed-`c` exponential display for every small `N ≥ 2`. |
| Theorem B.18: multiplication/circuit correlation | [MultiplicationFootprint.middleBit_signCorrelationBound](MultiplicationFootprint.lean); [FourierCorrelation.circuit_correlation_le](FourierCorrelation.lean) | Explicit finite rate: `sqrt(9 N² (4/5)^N) + sqrt(Tal.tailBound d s (N/8+1))`. It combines the proved low-degree estimate with the locally proved Tal theorem. This is the quantitative counterpart of the paper's asymptotic exponential rate, not a declaration copying its `min(1, …)` display. |

### FAQ propositions: information-theoretic coverage

| Paper result | Lean theorem(s) | Coverage and qualifications |
| --- | --- | --- |
| Proposition A.1: pairwise leakage without bit recovery | [LocalUnrecoverability.no_individual_bit_recoverable](LocalUnrecoverability.lean); [LocalUnrecoverability.pairedTrace_information](LocalUnrecoverability.lean) | For even input length `N`, adjacent-pair XORs reveal exactly `N/2` information bits, while every unrestricted predictor of an individual input bit succeeds with probability exactly `1/2`. This is the finite trace construction, not a proved efficient one-layer Transformer implementation. |
| Proposition A.2: complement-symmetric computation | [LocalUnrecoverability.canonicalSymmetricTrace_no_bit_recoverable](LocalUnrecoverability.lean); [LocalUnrecoverability.canonicalSymmetricTrace_information](LocalUnrecoverability.lean); [LocalUnrecoverability.canonicalSymmetricTrace_output](LocalUnrecoverability.lean) | The complete finite visible object reveals exactly `N-1` bits, gives no individual-bit advantage, and supports correct private-pivot output selection. The claimed efficient Turing/Transformer packaging and its `O(T log T)` resource bound are not formalized for this FAQ construction, as excluded from the requested scope. |

### Definitions, assumptions, and conventions

| Paper reference | Lean declaration(s) | Status |
| --- | --- | --- |
| Definitions B.1--B.2: Transformer and parameter count | [TransformerAC0.FixedPrecisionTransformer](TransformerAC0.lean); [TransformerAC0.Architecture.parameterCount](TransformerAC0.lean) | Matrix-level finite-precision semantics and the paper's parameter-count formula; actual rounded numerical operations are provided by [CanonicalArithmetic.arithmetic](CanonicalArithmetic.lean). |
| Assumption 3.4 / Definition B.12: local PRG and security | [PrivatePolynomialTime.SeedIndexedGenerator](PrivatePolynomialTime.lean); [Encryption.NC0GeneratorFamily.IsPseudorandom](Encryption.lean) | Explicit generator/security arguments, not an existence proof or hidden axiom. The Lean family uses `floor(n^stretch)` output length rather than the definition's ceiling. Goldreich's five-locality is checked by [Encryption.goldreichGenerator_is_five_local](Encryption.lean); its security is not proved. |

The remaining numbers B.7, B.10, and B.13 are remarks, not omitted theorems.
The formal matrix driver uses greedy decoding; the stochastic-decoding
extension discussed in Remark B.7 is not a separate proved extension here.
The public/covert entropy statements allow the correlations discussed in
Remark B.10, and PRG security uses the nonuniform circuit convention of
Remark B.13.

Further conventions matter when comparing formulas. Fourier coefficients
are normalized uniform expectations; `Tal.tailWeight f k` includes degree
`k`, whereas [FourierCorrelation.lowerWeight](FourierCorrelation.lean)
uses degrees strictly below its cutoff. Thus `N/8+1` corresponds to the
low-degree cutoff `N/8`. For multiplication, `N` is one operand's bit length
and the full input has `2N` bits. Length/source-coding statements for native
traces include the terminating separator and use the full alphabet's
`log₂ |Γ|`; privacy excludes the plaintext output suffix. These conventions
and finite quantitative bounds should be used instead of treating the map
as a claim of syntactically identical paper and Lean statements.

## Exact external premises

Exactly one research-level premise remains for the current encrypted core
results: an ordinary seed-indexed NC⁰ PRG with its security theorem. The
generator and security are explicit theorem arguments, not hidden Lean
axioms. Tal's theorem and the required near-linear multiplication algorithm
are proved locally. No research-level premise remains for Tal itself or
the seed-free constructions.
Ordinary Lean/mathlib module imports are separate from this research boundary.

### Tal's Fourier-tail theorem: proved locally

The statement `Tal.FourierTailTheorem` is defined in
[Tal.lean](Tal.lean) and proved by
[`TalComplete.fourierTailTheorem`](TalComplete.lean). For every input dimension, one-output Boolean circuit,
depth bound `d`, gate-count bound `s > 1`, and degree threshold `k`, it states:

```text
sum_{|S| >= k} (FourierCoefficient(f, S))^2
  <= 2 * 2^(-k / (216^d * (log_2 s)^(d - 1)))
```

Here `f` is the circuit's sign function, the Walsh coefficients are normalized
using the uniform input distribution, and `d - 1` is natural-number
subtraction as in `Tal.tailBound`. This is the general upper-tail statement,
not just its parity specialization. The parity correlation consequence and
the elementary middle-multiplication-bit Fourier estimate are proved locally.

The complete theorem has no arguments:

```lean
theorem TalComplete.fourierTailTheorem : Tal.FourierTailTheorem
```

It assumes no Tal, switching, encoding-existence, normalization, raw-Fourier,
or circuit-induction theorem. Its kernel dependencies are exactly `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx` or custom axiom.
It covers all depths and all circuits in the original shared-circuit DSL,
not just formulas or depth-zero/one circuits.

#### Local proof components

[TalRestriction.lean](TalRestriction.lean) now proves the exact normalized
coordinate-restriction coefficient identities, their energy identity, and
the exact one-coordinate random-restriction Fourier-weight transfer,
Tal's single-coordinate tail inequality (Lemma 11), the adaptive
restriction-tree tail bound (Lemma 13), and vanishing of Fourier coefficients
above a decision tree's depth. These hold for real-valued functions and take
no Tal argument. [TalNumerics.lean](TalNumerics.lean) proves the prefactor
absorption (Claim 17), `60d * 192^(d-1) <= 216^d`, the logarithm/denominator
comparisons, and Theorem 18's final arithmetic implication. Its raw-bound
hypothesis is explicitly a hypothesis, not a newly imported theorem.

[TalRandomRestriction.lean](TalRandomRestriction.lean) defines the actual
independent finite product distribution of restrictions and proves its
normalization and probability bounds. It proves both coefficient-moment
identities (Tal's Fact 6), exact spectral upper-tail transfer, and the
binomial law for the number of surviving coordinates (Fact 7). The transfer
is connected to ordinary `Nat.choose` binomial masses, not an abstract
spectral certificate.

[TalSecondMoment.lean](TalSecondMoment.lean) now proves the missing numerical
lower-tail estimate directly: survival counts with mean at least one exceed
half their mean with probability at least `1/8`. This uses finite weighted
Cauchy--Schwarz and the exact first/second moments, with no binomial-median
import. It gives the unconditional Fourier transfer
`W^{>=k}[f] <= 8 E[W^{>=floor(kp/2)}[f|rho]]` when `kp >= 1`.

The checked single-formula switching proof is now vendored in
[Complexitylib/](Complexitylib/README.md), with its finite circuit dependencies
under [Cslib/](Cslib/). [TalDecisionTree.lean](TalDecisionTree.lean) connects
its global-coordinate Boolean trees to our Fourier degree bound, including
trees with repeated queries. [TalSwitching.lean](TalSwitching.lean) identifies
the two restriction distributions pointwise and proves the unconditional
width-`t` DNF **and** CNF base cases:
`W^{>=k}[f] <= 16 * 2^(-k/(20t))`, for `t > 0`.

[TalCommonTree.lean](TalCommonTree.lean) defines the genuine common partial
tree predicate and proves the adversarial-answer step used between encoding
phases: after a prescribed sequence of queries, some answer transcript
preserves common-tree hardness up to the number of queries consumed. It does
not replace the shared tree by a union bound on separate decision trees.
[TalCanonicalCompletion.lean](TalCanonicalCompletion.lean) completes an
actual canonical path at a source-term boundary, with at most `t` extra
queries. [TalFamilyWitness.lean](TalFamilyWitness.lean) now constructs a
length-`D` witness from every bad common-tree restriction. It proves that its
queries are distinct and initially live, bounds its number of phases by
`ceil(D/(s+1))`, and proves the exact support/count and probability-mass
change of its satisfying extension. Witness existence is a proved result,
not an assumed certificate interface.

[TalFamilyAdvice.lean](TalFamilyAdvice.lean) proves the finite index/advice
counts. [TalBlockAdvice.lean](TalBlockAdvice.lean) also proves a simpler
`(3t)^D` sorted-block count without any mismatch condition.
[TalBlockPacking.lean](TalBlockPacking.lean) packs actual canonical term
blocks into that finite advice. [TalTracePrefix.lean](TalTracePrefix.lean)
and [TalRecoverableWitness.lean](TalRecoverableWitness.lean) prove the
recoverable phase boundaries for witnesses of the genuine bad event.
[TalFamilyEncoder.lean](TalFamilyEncoder.lean) stores only global answer
bits, padded family indices, and sorted source-term positions/difference
bits. [TalFutureReplay.lean](TalFutureReplay.lean),
[TalPhaseSplit.lean](TalPhaseSplit.lean),
[TalFamilyFrames.lean](TalFamilyFrames.lean), and
[TalFamilyTranscript.lean](TalFamilyTranscript.lean) prove canonical replay
in the presence of later-phase crumbs, splitting of the packed transcript,
and the exact global-answer state update.
[TalFamilyDecoding.lean](TalFamilyDecoding.lean) proves that the finite-advice
decoder is a left inverse on every recoverable witness.

[TalMultiSwitching.lean](TalMultiSwitching.lean) now proves the actual
common-tree family switching theorem, including injectivity of the chosen
bad-event encoder and the weighted probability bound. For a family of `m > 0`
width-`t > 0` DNFs, `m <= 2^(s+1)`, and `0 <= p < 1`, it proves

```text
Pr[no common tree of depth <= D-1 with leaf depths <= s]
  <= m * (24*p*t/(1-p))^D.
```

The exact division-free form is also proved for the endpoint parameters
`p=0,1`. No encoder-existence, recoverability, injectivity, or switching
hypothesis is assumed. This is a shared adaptive tree theorem, not just
simultaneous separate trees.
[TalCommonTreeFourier.lean](TalCommonTreeFourier.lean) connects these same
global-coordinate trees to the Fourier-tail adaptive tree bound, including
repeated queries and already-fixed variables.

[TalSwitchingNumerics.lean](TalSwitchingNumerics.lean) chooses `p=1/(30t)`,
proves the geometric bound and all floor losses, and absorbs the family-size
prefactor. At `s=Nat.log 2 (2m)` and `D=floor(k/(360t))`, the actual bad
probability is at most `2 * 2^(-k/(1440t * log_2(2m)))`.
[TalMixedSwitching.lean](TalMixedSwitching.lean) extends this to a mixed
DNF/CNF family without doubling its size: leaf decision-tree depth is
invariant under independent output complementation of family members.
[TalTreeNormalForm.lean](TalTreeNormalForm.lean) constructs both a DNF and a
CNF of width at most `s` from every depth-`s` decision tree, including repeated
coordinates; contradictory branch terms are discarded.

[TalSignedCircuit.lean](TalSignedCircuit.lean) compiles the original circuit
language to signed free wiring and AND/OR gates. It proves exact evaluation,
nonincreasing depth, and nonincreasing gate count, retaining serial sharing
and bundled parallel branches. Negation elimination therefore needs no
factor-two gate overhead. It also proves the exact displayed Tal conclusion
for all depth-zero circuits, with no Tal premise. The complete shared-gate
normalization is supplied by `TalSharedCircuit.lean`, described below.
[TalShallowCircuit.lean](TalShallowCircuit.lean) proves the exact displayed
Tal conclusion for all original circuits of depth at most one. It constructs
width-one DNF/CNF views through serial, parallel, and bundled sharing, then
uses the checked switching base and prefactor absorption. Its combined
`tailWeight_le_of_depth_le_one` theorem covers both depth-bound values `0,1`
without a Tal, normalization, or raw-Fourier-bound premise.
[TalOptimizedNumerics.lean](TalOptimizedNumerics.lean) checks the arithmetic
for the factor-eight route, including `82d * 180^(d-1) <= 216^d`. Like the
original numerical module, its raw-bound reduction is a numerical implication.
The complete proof uses the all-block route below.
[TalBroadNumerics.lean](TalBroadNumerics.lean) checks the all-block route's
`82d * 144^(d-1) <= 216^d` and the corresponding raw-bound normalization,
using the original gate budget and scale `72 log_2(2m)`. The raw Fourier
hypothesis of this arithmetic lemma is now supplied by the local circuit
induction, rather than an external assumption.

[TalGateNetwork.lean](TalGateNetwork.lean) defines signed references and
strictly ranked shared gates with explicit AND/OR evaluation equations. Its
`Model.lower` constructs the actual depth-lowered network at each common-tree
leaf: bottom shallow trees become bounded-width normal forms, the next gate
layer is flattened, and higher ranks decrease. The gate set is unchanged.
[TalSharedCircuit.lean](TalSharedCircuit.lean) constructs this representation
from the original circuit DSL, including serial sharing, parallel branches,
and bundles. It proves exact evaluation, depth control, and one node per
gate; `exists_model` fits the representation into the original size bound.
No circuit-normalization certificate is assumed.

[TalNetworkCut.lean](TalNetworkCut.lean) connects the actual bottom-layer
family to common-tree leaves and the Fourier tree bound.
[TalNetworkFourier.lean](TalNetworkFourier.lean) proves `raw_tail_bound`
by induction on gate rank. It combines the checked base case, mixed-family
common-tree switching probability, actual leaf depth reduction, and
factor-eight random-restriction Fourier transfer. Its raw estimate is

```text
W^{>=k}[f] <= 16 * 17^h * 2^(-k / (20*t*(72*log_2(2m))^h)).
```

The compiler supplies `t=1` and `h=d-1`. [TalComplete.lean](TalComplete.lean)
then applies the checked numerical absorption to obtain precisely the
original `216^d` statement, without changing its circuit class, gate budget,
or constants. [TalConsequences.lean](TalConsequences.lean) provides
unconditional parity correlation, general circuit correlation, footprint,
and multiplication footprint/length entry points. The complete encrypted
task and multiplication headline theorems also use this local Tal proof.

These results are included in [Verification.lean](Verification.lean), which
checks their transitive kernel dependencies. Older parameterized helper
lemmas may still take `tal : Tal.FourierTailTheorem`; that argument can now
always be filled by the locally proved theorem and is no external premise.
The full integrated build and standard-axiom-only kernel audit passed on
2026-10-15; the complete local Tal theorem also passed a standalone axiom check.

To build Tal independently of the paper's encryption and multiplication
constructions, run `lake build TalComplete`. Its public interface and exact
axiom dependencies can be inspected with:

```lean
import TalComplete

#check TalComplete.fourierTailTheorem
#print axioms TalComplete.fourierTailTheorem
-- [propext, Classical.choice, Quot.sound]
```

The source proof is [Tal's CCC 2017 paper](https://doi.org/10.4230/LIPIcs.CCC.2017.15).
A web/source search on 2026-10-14 found related public Lean developments:
[formalcs/circuit-complexity](https://github.com/formalcs/circuit-complexity/tree/8b1a1afd4a816edb0ed0716f20ec739ab2c033d9),
[Quantyra/formal-switching-lemma](https://github.com/Quantyra/formal-switching-lemma/tree/f3d7bc8432186de8d99e894b308c4c0e6bf34fd1), and
[SamuelSchlesinger/complexitylib](https://github.com/SamuelSchlesinger/complexitylib/tree/add0aca8ee0d71e68969f2cb45cf91554a50f787).
Their sources provide single-formula switching results; the inspected
`complexitylib` finite-family result explicitly supplies only a union bound,
not the common partial tree needed here. No complete proof of the required
Tal theorem was found in these sources. The pinned `complexitylib` single
switching dependency closure has now been ported and checked locally; the
other repositories are not dependencies. No repository's unverified claim
has been substituted for a checked proof. The common-tree argument,
shared-circuit normalization, and full Tal induction are proved here.

### Sole external research premise: an NC⁰ generator and circuit security

The arguments are:

```lean
(generator : PrivatePolynomialTime.SeedIndexedGenerator stretch)
(secure : generator.IsPseudorandom)
```

[PrivatePolynomialTime.lean](PrivatePolynomialTime.lean) defines the family
type as `Encryption.NC0GeneratorFamily id (fun n => ⌊(n : ℝ) ^ stretch⌋₊)`.
Thus an `n`-bit uniform seed produces `floor(n^stretch)` output bits. Each
output bit depends on at most a fixed number of seed coordinates, independent
of `n`.

`Encryption.NC0GeneratorFamily.IsPseudorandom`, in
[Encryption.lean](Encryption.lean), quantifies over every nonuniform
polynomial-size Boolean circuit family. For each such monitor there must be
a negligible error function bounding, at every seed length, its absolute
distinguishing advantage between generator output and uniform output bits.
Negligibility means eventual decay faster than every inverse polynomial.

The elementary-task and multiplication constructions require `stretch > 1`.
The general polynomial-time construction with time exponent `k >= 1`
requires `stretch > k`. The premise supplies the generator itself as well as
its security; neither existence of a secure family nor security of the
concrete Goldreich candidate is proved here. Reindexing to the simulation's
chosen seed lengths, pad-prefix security, seed and capacity bounds, and
whole-reasoning-prefix privacy are derived locally, not additional imports.
Output correctness uses the local generator data but does not require its
security proof.

### Multiplication is now proved locally, not imported as a premise

The replacement uses classical Schönhage–Strassen multiplication, avoiding
the sharper Harvey–van der Hoeven theorem. The 49 proof modules under
[IntegerMultBounds/](IntegerMultBounds/) include exact modular FFTs, recursive
product correctness, physical stream/counter routines, compilation to a
fixed finite-state 64-tape machine, halting, and actual transition counts.
The classical cost bound is `O(N log N log log N)`; our downstream interface
uses the simpler, proved envelope:

```text
time(N) <= C * (N + 1) * (floor(log_2(N + 1)) + 1)^2
context(N) <= C' * (N + 1) * (floor(log_2(N + 1)) + 1)^3
```

[VerifiedMultiplicationSource.lean](VerifiedMultiplicationSource.lean) defines
the fixed machine and proves `time_bound`, `full_product` (all `2N` product
bits), and `middle_bit` with no research premise.
[MultiplicationMachineBridge.lean](MultiplicationMachineBridge.lean) identifies
its transitions with our local multitape semantics and adds an absorbing
halt state for padding to the compiler's horizon.

The input representation is explicitly prepared: padded operand words and
a public unary size ruler, with all heads initially at zero.
[SchonhageInitializer.lean](SchonhageInitializer.lean) proves this preparation
uses only constants and individual raw input bits, including padding and
separators. [MultitapeLiteralInitialization.lean](MultitapeLiteralInitialization.lean)
turns those sources into checked depth-one prompt literals. No product,
future machine configuration, or simulation certificate is initialized.

[VerifiedPlainMultiplication.complete](VerifiedPlainMultiplication.lean)
has no theorem arguments. [VerifiedMultiplication.complete](VerifiedMultiplication.lean)
takes only `stretch > 1`, the ordinary seed-indexed generator, and its
security. Both use native four-token matrices, one layer, fixed heads and
precision, and derived polynomial dimension/parameter bounds. The encrypted
version also proves full-reasoning-prefix privacy and the same-model seeded
information/expected-length bounds. [PolylogSeedBudget.lean](PolylogSeedBudget.lean)
proves that any fixed polylogarithmic overhead still permits a sublinear
seed for every stretch greater than one.

The classical proofs are vendored from
[platypii/integer-mult-bounds-lean](https://github.com/platypii/integer-mult-bounds-lean/tree/9b148a008183b1342e134af1270d3a7dafad4a9c),
commit `9b148a008183b1342e134af1270d3a7dafad4a9c`, with
[MIT attribution](IntegerMultBounds/LICENSE), and ported to our pinned
Lean/mathlib version. Their proof sources are included here and checked
locally; no additional external Lean package is required. The upstream
project's stronger unfinished `Machine.EndToEnd` target is neither invoked
nor assumed by this development.

The optional older sharp-bound interfaces still accept
`FastMultiplication.MultitapeNLogNTheorem`, as defined in
[FastMultiplication.lean](FastMultiplication.lean). That statement remains
unproved here but is not a premise of either replacement headline theorem.

### Which results need which premises?

| Result | External research premises |
| --- | --- |
| Seed-free parity, full S₅, and positive addition (`PlainTasks`) | None |
| Seed-free whole-word Turing simulation (`PlainBinaryWord.whole_function_correct`) | None; takes an ordinary source-machine correctness specification |
| Seed-free multiplication (`VerifiedPlainMultiplication.complete`) | None |
| Tal's full Fourier-tail theorem (`TalComplete.fourierTailTheorem`) | None |
| Tal-based footprint, information, and length lower bounds (`TalConsequences` and existing reductions) | None; Tal is proved locally |
| Encrypted whole-word simulation and privacy (`ExactBinaryWord`) | Generator data for construction; PRG security for privacy |
| Complete encrypted elementary tasks (`ExactTasks.elementary_tasks_complete`) | Secure NC⁰ PRG only |
| Complete encrypted multiplication (`VerifiedMultiplication.complete`) | Secure NC⁰ PRG only |
| Optional sharper `O(N log² N)` multiplication interfaces | Additionally require `FastMultiplication.MultitapeNLogNTheorem`; outside the current `N * polylog(N)` completion requirement |

The development is self-contained relative to the permitted PRG premise.
Computational privacy remains conditional on PRG security; it is not an
unconditional cryptographic theorem. The kernel audit in
[Verification.lean](Verification.lean) rejects `sorryAx` and every axiom
except Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
Because the external premises are explicit arguments, passing that audit
does not establish the premises themselves.

Efficient FAQ constructions are outside the requested scope and are not an
additional imported premise. The finite information-theoretic FAQ results
are proved locally in [LocalUnrecoverability.lean](LocalUnrecoverability.lean).

## Formalized results and proof components

Information and length bounds are explicit finite inequalities, rather than
informal asymptotic notation.
Variable-length full-vocabulary autoregressive fibers and their
information/expected-length consequences permit the same matrices to be
restricted to growing causal prefixes; `CausalToken.lean` identifies them
with the native driver. The existing complete Boolean source protocol is
connected to the concrete first-separator seeded footprint proof.
In particular, the older finite-configuration simulator below does not establish
the paper's polynomial-size or binary-length upper bounds.

The concrete replacements for the former probability-law certificates are
in `FiniteInformation.lean`, `ConcreteReasoning.lean`, `SeededToken.lean`, and
`PolynomialEncryption.lean`. `TokenSymbolic.lean` gives full-uniform
alphabet versions of the `S₅` and `[100]` lower bounds for actual greedy
full-vocabulary, separator-terminated matrix traces. See
`SimulationSizeAudit.lean` for a proved size obstruction to the old simulator
shortcut.

The complete proof of the elementary multiplication Fourier estimate is in
`ElementaryMultiplication.lean`. It follows the appendix directly:

1. Define the half-period sign `s_N` on `ZMod (2^N)` and prove that
   `s_N(xy)` is exactly the sign of product bit `N - 1`.
2. Expand `s_N` in additive Fourier characters modulo `2^N`.
3. Split its DFT into two half-periods.  Nonunit (even) frequencies vanish;
   the remaining coefficients form geometric sums whose `l¹` norm is at
   most `3N`.
4. Prove directly from finite Parseval that each phase matrix
   `exp(2π i axy / 2^N)` has operator norm `sqrt(2^N)`.
5. Conclude the appendix's spectral estimate
   `||A_N|| ≤ 3 N sqrt(2^N)` and the pointwise Walsh bound
   `|F̂(R,S)| ≤ 3N / sqrt(2^N)`.
6. Sum over low-degree frequencies to obtain the explicit finite bound
   `W_{≤ N/8} ≤ 9 N² (4/5)^N`, hence exponential decay.

The main declarations are:

- `productSign_eq_middle_bit`
- `signDFT_eq_geometric`
- `sum_norm_signCoeff_le`
- `multiplication_spectral_bound`
- `norm_fourierCoeff_le`
- `middle_bit_lowDegreeWeight_bound`
- `middle_bit_fourier_resilience`

`TransformerAC0.lean` formalizes the appendix's other translation step.  It
defines explicit unbounded-fanin AND/OR/NOT circuits with shared intermediate
wires; constructs fixed-arity truth-table circuits; derives and compiles
star-free rounded-sum programs; and assembles embedding, attention, softmax, rounding,
ReLU/MLP, and readout without a realization hypothesis.  The Transformer
structure contains only matrices, finite scalar operations, embedding and
readout parameters, a total order on scalar encodings, and the paper's
order-preservation law for rounded addition.  It contains no circuit or
star-free-language certificate.  Its `run` function executes the actual
left-to-right rounded-addition fold and is an independent matrix semantics, not an
evaluation of the compiled circuit.  Lean proves each generated stage agrees
with that semantics.  The readout constructs every logit from the full
`D × |V|` unembedding matrix, compares them with finite truth-table circuits,
and implements deterministic greedy tie-breaking before returning the output
label.  Its main results are:

- `Circuit.eval_ofPredicate`
- `Circuit.depth_ofPredicate_le_three`
- `StarFree.eval_compile`
- `StarFree.depth_compile_le`
- `StarFree.gateCount_compile_polynomial`
- `OrderedAddition.LocalDivisor.card_lt`
- `OrderedAddition.exists_aperiodic_fiberExpressions`
- `OrderedAddition.OrderedEnd.isAperiodic`
- `FixedPrecisionArithmetic.roundedSumExpression_correct`
- `FixedPrecisionArithmetic.eval_sumCircuit`
- `FixedPrecisionTransformer.compile_correct`
- `FixedPrecisionTransformer.compile_depth_le`
- `FixedPrecisionTransformer.compile_depth_le_fixed`
- `FixedPrecisionTransformer.compile_depth_linear`
- `FixedPrecisionTransformer.compile_gateCount_le_total`
- `TransformerGateCost.total_polynomial`
- `polynomial_size_translation`
- `fpt_to_ac0`

`MatrixReadout.lean` additionally proves that the Boolean readout labels
classify the actual least-indexed maximum-logit vocabulary token. Scalar
comparison is derived from the scalar encoding order, not supplied as an
arbitrary Boolean operation. `CanonicalArithmetic.lean` proves that this
order is exactly numerical order on its signed fixed-point lattice.

`OrderedAddition.lean` proves the missing algebraic-language step rather than
postulating it: local divisors are monoids, remain aperiodic, and strictly
decrease in cardinality; the resulting well-founded Schützenberger induction
constructs a star-free expression for every fiber of a finite aperiodic
monoid.  It also proves directly that finite ordered transformation monoids
are aperiodic.  These results turn the rounded-addition order law into the
concrete expressions consumed by `StarFree.compile`.

`CanonicalArithmetic.lean` defines signed fixed-point scalars on a finite
equally spaced lattice. Addition, multiplication, real exponentiation,
division, and ReLU are rounded to the nearest lattice point with endpoint
saturation. It proves the rounded-addition order law, exact rounding of
representable values, and agreement of the encoding order with numerical
order. `CanonicalArithmetic.matrix_transformer_to_ac0` specializes the
compiler to this actual numerical arithmetic.

The polynomial-size theorem uses the paper's exact parameter count
`(3/2)|V|D + (3LH + 2L)D²` (with the even width represented as
`D = 2 * halfWidth`) and derives existential coefficient/exponent witnesses
for a polynomial in `M + N`; neither witness is defined using the generated
circuit's size.  The depth constant depends only on fixed scalar precision
(the derived expressions are fixed once the arithmetic is fixed), not on context length, width, heads,
vocabulary, or matrix entries.

`Footprint.lean` proves the parity footprint theorem from that circuit
interface and Tal's general AC⁰ Fourier-tail theorem.  It formalizes
finite uniform transcript probabilities and Shannon mutual information,
proves parity is balanced, converts sign correlation to the required `0/1`
indicator correlation, bounds every transcript fiber, and derives the paper's
quantitative lower bound.  Its main declarations are:

- `indicatorParityCorrelationBound_of_sign`
- `ParityTrace.transcriptProbability_le_of_correlation`
- `ParityTrace.entropy_ge_neg_log_maxProbability`
- `footprint_from_sign_correlation`
- `footprint_from_tal`
- `parity_footprint`
- `footprint_information_lower_bound`
- `footprint_tradeoff_of_sign_correlation`
- `footprint_theorem`

`Autoregressive.lean` closes the formerly abstract fixed-prefix step.  It
executes the matrix-level fixed-precision Transformer autoregressively,
substitutes each fixed candidate prefix into the compiled circuit, and derives
the transcript/answer fiber family automatically.  `TaskFootprint.lean`
generalizes the fiber argument to arbitrary Boolean targets, including target
bias.  Main declarations include:

- `Autoregressive.FixedPrecisionGenerator.generatedToken`
- `Autoregressive.FixedPrecisionGenerator.eval_fiberCircuit`
- `Autoregressive.FixedPrecisionGenerator.explicitFiberCircuitFamily`
- `Autoregressive.FixedPrecisionGenerator.footprint`
- `Autoregressive.FixedPrecisionGenerator.task_footprint`
- `TaskFootprint.footprint`

`TokenAutoregressive.lean` handles the full vocabulary directly. Every step
runs the same matrices (optionally restricted to a causal prefix) and emits
their actual greedy token; the visible word
ends at the first separator. Candidate circuits check each payload token,
the separator, and the next answer token. Their depth and gate bounds are
derived from the architecture/compiler, not assumed. Source coding includes
the separator and has the paper's denominator `log₂ |Γ|`. The older binary
payload variants remain in `TerminatedAutoregressive.lean` and
`TerminatedSymbolic.lean`.

- `TokenAutoregressive.Generator.eval_fiberCircuit`
- `TokenAutoregressive.Generator.fiberCircuit_depth_le`
- `TokenAutoregressive.Generator.fiberCircuit_size_le`
- `TokenAutoregressive.Generator.footprint`
- `TokenAutoregressive.Generator.expected_length_lower_bound`
- `ConcreteReasoning.token_multiplication_expected_length`

`FourierCorrelation.lean` proves Walsh orthogonality, inversion, Parseval, and
the complementary-tail Cauchy--Schwarz inequality.  It combines a target's
low-degree mass with Tal's circuit high-degree tail.  In
`MultiplicationFootprint.lean`, an explicit equivalence transports the
residue-pair coefficients from `ElementaryMultiplication.lean` to the ordinary
`2N`-bit Boolean cube.  The result is then composed with the autoregressive
fiber theorem and the entropy-capacity bound:

- `FourierCorrelation.fourier_inversion`
- `FourierCorrelation.correlation_eq_sum_fourier`
- `FourierCorrelation.circuit_correlation_le`
- `MultiplicationFootprint.fourierCoefficient_combined`
- `MultiplicationFootprint.middleBit_signCorrelationBound`
- `MultiplicationFootprint.autoregressive_footprint_explicit`
- `MultiplicationFootprint.autoregressive_binary_length_lower_bound_explicit`

`Tal.lean` states the theorem in the greater generality used elsewhere in the
appendix: normalized Walsh coefficients and the complete upper-tail bound
`W^{≥k}` for every degree threshold.  It then proves the specialization to
parity correlation, and `TalComplete.lean` proves the full statement. The key declarations are `Tal.levelWeight`,
`Tal.tailWeight`, `Tal.FourierTailTheorem`, `Tal.parityCorrelation_sq_le`, and
`Tal.abs_parityCorrelation_le_sqrt_tailBound`.

`HiddenReasoningTax.lean` retains the original algebraic entropy-profile
interface. Its results are conditional on the entropy-law and source-coding
fields supplied there. The concrete replacement is
`ConcreteReasoning.hidden_reasoning_tax`: an explicit finite joint
distribution determines all random variables and information quantities;
recoverability is an equality of actual maps; uniformity is an equality of
probability masses. `FiniteInformation.lean` proves entropy monotonicity,
the exact entropy tradeoff
`H(public) + I(covert;(public,trace)) - I(covert;public) <= H(trace)`, and
the separator-terminated Kraft/source-coding bound, including variable
expected lengths. No entropy-law or source-coding certificate is assumed by
the replacement. Its generic formulation takes the computation footprint as a
compositional premise. `ConcreteReasoning.token_hidden_reasoning_tax` derives
that footprint directly from the locally proved Tal theorem and the actual
terminated matrix execution, so no research-level import is needed. Its
parameterized interface can be instantiated with
`TalComplete.fourierTailTheorem`. The legacy declarations are:

- `HiddenReasoningTax.EntropyProfile.entropy_tradeoff`
- `HiddenReasoningTax.hidden_reasoning_tax`
- `HiddenReasoningTax.hidden_reasoning_tax_of_footprint`
- `HiddenReasoningTax.hidden_reasoning_tax_of_sign_correlation`
- `HiddenReasoningTax.hidden_reasoning_tax_of_tal`
- `HiddenReasoningTax.hidden_reasoning_tax_quantitative`

`EntropyCoding.lean` proves the finite Shannon entropy upper bound rather than
assuming a source-coding certificate, and composes it with the actual
autoregressive model.  `PublicReasoningTax.lean` gives a fully concrete
independent-uniform public/covert specialization: recoverability makes public
transcript fibers disjoint, so the public-input cost and hidden-computation
cost combine before the fixed-alphabet entropy cap.  Main declarations are:

- `EntropyCoding.transcriptEntropy_le_log_card`
- `EntropyCoding.fixedLength_entropy_le`
- `EntropyCoding.autoregressive_binary_length_lower_bound`
- `PublicReasoningTax.PublicBooleanTrace.global_probability_eq_fixed_div`
- `PublicReasoningTax.PublicBooleanTrace.fixedLength_lower_bound`

`TaskReductions.lean` proves the appendix's other two reductions, including
their end-to-end autoregressive footprint and length corollaries.  The `S₅`
proof uses the actual permutation-sign homomorphism; addition uses the actual
least significant bit of the natural-number sum:

- `TaskReductions.s5StateTrackingParity_eq_product_sign`
- `TaskReductions.s5_reduces_parity`
- `TaskReductions.iterated_addition100_reduces_parity`
- `TaskReductions.s5_autoregressive_binary_length_lower_bound`
- `TaskReductions.iterated_addition_autoregressive_binary_length_lower_bound`

The binary-embedding results above are supplemented by full-alphabet
versions in `UniformTaskFootprint.lean`. `TaskReductions.s5Pairing` is an
explicit equivalence `S₅ ≃ Bool × EvenS5`, with `|EvenS5| = 60`.
`additionPairing100` is an explicit equivalence `[100] ≃ Bool × [50]`.
For a matrix Transformer with symbolic one-hot input wires, fixing the pair
labels leaves literal Boolean input wires. The compiler derives each slice's
fiber circuits, and the probability bound is averaged over all pair labels.
The information in these statements is actual Shannon mutual information
under the uniform full symbolic input distribution:

- `UniformTaskFootprint.s5_uniform_footprint`
- `UniformTaskFootprint.addition100_uniform_footprint`
- `UniformTaskFootprint.s5_uniform_binary_length_lower_bound`
- `UniformTaskFootprint.addition100_uniform_binary_length_lower_bound`

`TokenSymbolic.lean` carries the same slice averaging through genuine
full-vocabulary variable-length execution. Its length bound includes the
separator and uses `log₂ |Γ|` for both full task alphabets:

- `TokenSymbolic.s5_uniform_expected_length`
- `TokenSymbolic.addition100_uniform_expected_length`

`Encryption.lean` formalizes the appendix's encrypted-CoT theorems.  It gives
the `NC⁰` PRG assumption an explicit nonuniform polynomial-circuit meaning,
formalizes Goldreich's five-local predicate, and proves the full security
reduction: PRG security passes to a trace-length prefix, survives XOR with
each fixed plaintext trace, and bounds prediction of every input predicate
under every finite input distribution by the best prior-only guess plus the
PRG advantage.  It also proves that private randomness reduces the
information-theoretic footprint by at most the seed length and connects that
claim directly to the existing footprint and Tal theorems.  Main declarations
include:

- `Encryption.NC0GeneratorFamily.IsPseudorandom`
- `Encryption.goldreichGenerator_is_five_local`
- `Encryption.secure_prefix`
- `Encryption.encryptedTrace_pointwise_secure`
- `Encryption.prediction_le_prior`
- `Encryption.randomness_cannot_erase_footprint`
- `Encryption.randomness_footprint_of_tal`
- `Encryption.encrypted_trace_no_readability_of_local_generator`
- `Encryption.encrypted_trace_leakage_and_security`

The original randomness lemmas above use `PrivateRandomnessProfile`.
`ConcreteReasoning.SeededGenerator.randomness_footprint_of_tal` replaces it
with actual matrix executions and the explicit uniform distribution on
input/seed pairs. Entropy concavity and finite cardinality prove the loss of
at most one information bit per seed bit. The expected-length consequence
uses the proved separator coding inequality.

`SeededToken.lean` strengthens the model binding: private bits are additional
input wires of one matrix Transformer. Fixing the seed changes only literals;
architecture, weights, vocabulary, and separator remain identical. For the
actual uniform independent input/seed distribution it proves the `r`-bit
information loss, no seed discount in expected token length, and the
correlated public/covert length tax. The parity and middle-multiplication-bit
versions use Tal and the proved elementary Fourier estimate, respectively:

- `TokenAutoregressive.Generator.fixSeed_transcript`
- `TokenAutoregressive.Generator.seeded_footprint`
- `TokenAutoregressive.Generator.seeded_expected_length_lower_bound`
- `TokenAutoregressive.Generator.seeded_public_length_tax`
- `TokenAutoregressive.Generator.seeded_multiplication_footprint`
- `TokenAutoregressive.Generator.seeded_multiplication_expected_length_lower_bound`

`PolynomialEncryption.lean` connects privacy directly to
`NC0GeneratorFamily.IsPseudorandom`. It constructs the polynomial-size prefix
and XOR circuits and uses a maximizing plaintext at each length as
nonuniform advice. The resulting single negligible error works uniformly
over all plaintexts; no monitor-class closure certificate is supplied. Its
compound leakage/privacy theorem refers to the same concrete ciphertext
distribution in both conclusions:

- `ConcreteReasoning.encrypted_autoregressive_footprint`
- `ConcreteReasoning.randomness_expected_length_lower_bound`
- `PolynomialEncryption.pointwise_security`
- `PolynomialEncryption.no_readability`
- `PolynomialEncryption.leakage_and_privacy`

`ObliviousSimulation.lean` defines input-dependent bounded multitape
computation and a finite one-cell semantic simulator. The simulator stores
the complete source configuration in its finite control and proves exact
configuration preservation. This is a semantic shortcut, not an efficient
oblivious-machine compilation. `SimulationSizeAudit.lean` proves that storing
`m` Boolean tape cells this way requires at least `m` bits per token and
`2^m` token values. Hence a bound on its abstract event count does not imply
the claimed binary trace bound or polynomial vocabulary/model size.

The same module defines input-independent tape schedules, last-write
semantics, and a causal one-layer attention/local-map model. Every generated
token is proved equal to one attention round followed by the transition.
Its encrypted model adds attention
heads that retrieve exactly the local PRG seed dependencies; its single local map
decrypts the selected prior ciphertexts, applies the transition, and encrypts
the next token. Lean proves its generated trace equals the XOR ciphertext and
that its readout equals the plaintext computation.  The actual encrypted head
type has the stated constant cardinality, encryption adds no autoregressive
events when token width is fixed. These attention/local-map records alone
do not provide a numerical matrix realization or its resource accounting;
the checked efficient replacements are described below. The following
semantic/interface theorems are therefore not the complete
matrix-level upper bounds of the paper:

- `ObliviousSimulation.one_layer_oblivious_simulation`
- `ObliviousSimulation.compileInputDependent_traceToken`
- `ObliviousSimulation.inputDependent_to_one_layer_oblivious_simulation`
- `ObliviousSimulation.encryptedTransformer`
- `ObliviousSimulation.encryptedTransformer_flat_trace`
- `ObliviousSimulation.encryptedTransformer_output`
- `ObliviousSimulation.encryptOneLayerTransformer`
- `ObliviousSimulation.encrypting_cots_using_few_random_bits`
- `ObliviousSimulation.transformers_can_encrypt_reasoning`
- `ObliviousSimulation.one_layer_oblivious_simulation_with_overhead`
- `ObliviousSimulation.encrypted_oblivious_simulation_with_overhead`
- `ObliviousSimulation.inputDependent_to_encrypted_oblivious_simulation`
- `ObliviousSimulation.inputDependent_transformers_can_encrypt_reasoning`

The efficient replacement is being developed independently of that shortcut:
`ObliviousProgram.lean` provides fixed-address read/write/local instructions
with genuinely fixed finite control and a fixed cell alphabet. It constructs
last-access schedules and proves exact last-write semantics, a two-head
semantic compilation, and constant-width token encoding independent of tape
capacity. `ObliviousPhase.lean` defines a proper local source machine and the
recursive Pippenger--Fischer phase plan, proving exact source-step and
cell-linear work counts. `TapeRotation.lean` proves finite-window cyclic
rotations are invertible, leave outside cells unchanged, and commute with
every source transition and tape write under explicit boundary clearance.
`PhaseSemantics.lean` proves that the complete recursive compression phase
equals `2^j` source steps, and bounds the phase weights by
`10 T (log₂ T + 1)`. `ObliviousCopy.lean` implements conditional snapshot scans
with fixed-address read/modify instructions and one held symbol.
`RotationProgram.lean` expands both rotation directions into those scans,
proving exact whole-tape permutation and a linear instruction count.
`HeadMarker.lean` derives the compression choice by scanning a unique cell
marker. `CompressedTape.lean` composes that detection with the two-direction
rotation, preserving the marked source tape with fixed finite control.
`PhaseStack.lean` saves the compression choice in tape memory and loads it
for inverse expansion; outside-window stack slots survive nested rotations.
`LeafStep.lean` implements a source transition using three fixed marker reads
and five fixed cell updates, with only constant-size local registers. Its
complete event-token alphabet has exactly `72 |State| |Symbol|³` values,
independent of tape capacity and execution length.

`EfficientPhase.lean` now assembles all of these instructions into the full
recursive program, proves preservation of caller stack choices, and proves
the exact state-and-tape simulation theorem. The initial state is constant
and initialization copies only the raw input tape. Its exact event count is
`L(j) + 32 = (208 j + 40) 2^j`, giving
`L ≤ 992 T (log₂ T + 1)` at the padded power-of-two horizon. Its two-head
backend output equals the simulated source output. These are actual
instruction/event counts, not weights assigned to unexpanded primitives.
This module is a single-tape source compiler. `EfficientMatrix.lean` supplies its complete one-layer
matrix assembly and source-output theorem. No physical
unit-head-motion runtime theorem is claimed for the fixed-address backend.

The multitape extension now starts from `MultitapeTuring.lean`, a genuine
local unit-motion machine: transitions see only the state and one scanned
symbol per tape, not head coordinates or unscanned memory. Lean proves
head-distance bounds, transport of all writes under per-tape permutations,
joint finite-window rotation conjugacy, and halting padding.
`MultitapePhase.lean` proves that recursive per-tape compression semantics
preserves the complete configuration and simulates exactly `2^j` steps.
`TapeProgram.lean` transports the actual marker/rotation/choice-stack
instruction lists to tape/address pairs, proving exact selected-tape
execution, preservation of other tapes, saved choices, inverse expansion,
and unchanged instruction counts. `MultitapeLeaf.lean` supplies the full
`8 K + 1`-instruction joint source step: all scanned symbols are collected
before the shared transition, then all symbols/markers are updated. Its
register alphabet has `|State| 9^K |Symbol|^(2K)` values, independent of
horizon and tape capacity. `MultitapeBatches.lean` expands complete tape
compression/expansion batches, proving every tape is processed exactly once
and all saved choices and caller stack slots survive. The full recursive
`MultitapeEfficientPhase.lean` compiler preserves the source state, all heads
and every tape cell. Its exact count is
`L(j) + 32K = (208Kj + 40K + 1) 2^j`, and its derived event bound is
`4(248K+1) T (log₂ T + 1)`. `MultitapeMatrix.lean` connects this entire
compiler to the original numerical matrix Transformer, with one extra final
read of the actual computed output cell. Its raw-input adapter is a checked
depth-one literal circuit. `EncryptedMultitapeMatrix.lean` supplies the same
source-output theorem with on-the-fly matrix encryption and raw seed/input
initialization; privacy refers to that model's actual ciphertext trace.

`FastMultiplication.MultitapeNLogNTheorem` retains the optional sharper-bound
premise as the existence of one fixed finite-state, finite-alphabet,
unit-motion multitape machine, with raw input initialization, full binary
product correctness, terminal-state stuttering, and an `N log N` transition
bound. It is an explicit theorem argument, not an axiom. The checked
`padded_full_product` theorem derives correctness at the compiler's
power-of-two horizon, and `middleBit_eq` identifies its output with the
lower-bound task. No Transformer or oblivious-simulation theorem is smuggled
into this premise. `MultiplicationUpper.matrix_upper_bound` composes this
optional premise with the entire proved compiler and numerical model. It
computes the paper's lower middle multiplication bit with one layer, two
heads, fixed precision, and an explicitly derived `O(N log² N)` event count.
Actual hidden dimension and parameter count have derived polynomial bounds.

The numerical pieces are now independent of the old Boolean lookup shortcut:
`NumericalPrimitives.lean` proves exact supported integer operations and
rounded accumulation, including all intermediate prefixes.
`NumericalAttention.lean` executes the query/key inner product, rounded real
exponentiation, denominator sum, division, and weighted-value sum, proving
exact selected-value retrieval at a fixed two-bit signed precision for any
context length. `NumericalMLP.lean` constructs signed numerical weights,
constant-coordinate biases, ReLU pattern detectors, and the second output
matrix for any fixed finite local map. Its precision is fixed once that
local map's finite feature width is fixed, independently of execution length.
`RoutedMatrixCorrectness.lean` now assembles these proofs into an end-to-end
execution theorem for the actual numerical matrix Transformer.

`CausalMatrix.lean` restricts one parameter set to increasing causal context
prefixes, proving that all learned matrices and token embeddings stay
identical. `CausalMatrixCorrectness.lean` additionally proves that restricting
the input to a causal prefix preserves all existing-position hidden scalars,
logits, and greedy tokens, by induction through the numerical layers.
`CausalAutoregressive.lean` executes genuine greedy autoregression
on those prefixes and constructs exact candidate next-token circuits with a
common depth and polynomial-size budget. There is no supplied transition,
layer-function, or circuit-realization field in this causal model.

`RoutedMatrix.lean` contains the actual assembled numerical token/position
embeddings, Q/K/V matrices, MLP matrices, and unembedding in the original
`FixedPrecisionTransformer` type. It proves one-hot token embedding,
linear hidden-dimension growth and quadratic parameter-count growth in the
context window, with fixed layer/head counts and scalar precision. The
finite local-map truth table is a constant independent of that window.
`RoutedMatrixCorrectness.run_token_correct` proves the complete next-token
execution theorem: literal one-hot input, Q/K/V projection, causal rounded
softmax, both residuals, ReLU pattern detection, the output matrix, and greedy
unembedding. Every rounded sum has checked intermediate-prefix bounds. The
only input data are the static causal routing/opcode plan and finite local
map; no realization or numerical-correctness certificate is assumed.
`run_token_prefix_correct` uses that same parameter set on each shorter
literal context. `RoutedMatrix.autoregressive_correct` in
`RoutedAutoregressive.lean` proves the
entire local-map recurrence agrees with the existing growing-prefix greedy
matrix driver. `RoutedLocalMap.lean` constructs the truth table from any
finite opcode-controlled transition, proving that its feature decoding
recovers precisely the selected tokens and the static opcode.
`ObliviousMatrix.lean` now connects that constructor to the fixed-address
event program: one head reads preceding control, one reads the last cell
write, and the finite opcode selects the instruction's control/symbol update.
`generated_correct` proves that the real greedy autoregressive driver emits
the exact event trace; `output_correct` proves final-control readout.
The complete vocabulary is `|Control| + |Symbol| + |Control| |Symbol|`,
independent of addresses and horizon.

`EfficientMatrix.matrix_output` composes this with the entire recursive phase
compiler, starting from raw Boolean input cells and constant initial control.
`padded_matrix_output` handles stuttering terminal states. The same model has
two heads, one layer, fixed precision/alphabet, at most
`992 T (log₂ T + 1)` generated event tokens and at most twice that context
size. `inputEncoding_literal` and the depth-one `inputCircuit` prove that the
padded initialization copies only constants or single raw input literals;
it cannot conceal source simulation in preprocessing. Actual hidden dimension
and parameter count have derived polynomial bounds when source time is
polynomial. These remain single-tape, Boolean-readout results.

`LocalPRG.lean` derives each finite pad truth table from the local generator's
dependency neighborhoods. `RoutedSchedule.lean` extracts a strictly causal
source-index/opcode schedule from the already checked plaintext plan.
`EncryptedMatrix.lean` builds actual shared numerical Q/K/V, MLP and
unembedding matrices for the encrypted recurrence. The MLP retrieves raw
seed neighborhoods, computes the relevant PRG bits, decrypts the selected
prior events with their own event-time pads, performs the plaintext local
instruction, and encrypts the new event. Neither a future pad nor a future
control state is initialized. `generated_correct` proves the entire native
greedy driver emits these ciphertext packets; `output_correct` proves the
final answer; `transcript_eq_encryptedTrace` connects this same actual trace
to the verified PRG reduction. The vocabulary has `v + 2^v + 4` tokens and
the head count is `H + (H+1) v ell`, all constant for fixed plaintext
vocabulary `v`, head count `H`, and PRG locality `ell`.

`EncryptedObliviousMatrix.lean` composes this with the fixed-address program's
proved last-write semantics. `EncryptedEfficientMatrix.lean` supplies the
complete efficient single-tape source-to-encrypted-matrix theorem. Its
depth-one `inputCircuit` copies only raw input/seed literals or constants;
encryption adds no generation events. Its event and ciphertext-bit counts
are derived `O(T log T)` bounds, and actual matrix dimension and parameter
count have polynomial bounds when source time and seed length are polynomial.
`no_readability` applies PRG security to arbitrary input distributions and
predicates, deriving the polynomial trace-length condition from source time.

`EncryptedSerialization.lean` proves privacy for the complete emitted token
word under any fixed binary encoding, including a lossless code. The explicit
encoding circuit has depth at most three and size linear in trace length,
so every polynomial monitor of the full encoding has a polynomial ciphertext
monitor. This is a privacy/encoding reduction, not a claim that the current
matrix driver emits literal binary tokens. That generation obligation is now
handled separately by the following constructors.

`ScheduleMatrix.lean` realizes any static causal finite-opcode schedule by
the actual shared-matrix greedy driver. `BinarySchedule.lean` replaces every
finite-alphabet event by its fixed-width one-hot bit block, reconstructing
earlier selected events from their emitted bits. `BinaryMatrix.lean` proves
that the original numerical driver generates those literal binary tokens
and the correct final answer, with a literal-circuit prompt adapter.
`EncryptedBinaryMatrix.lean` emits just two fixed ciphertext packet tokens:
a single PRG bit swaps the two one-hot Boolean codewords. Security is proved
from the original one-bit-per-event PRG, not from a false claim that the
duplicated pad bits are pseudorandom. The actual visible bit word equals
plaintext XOR the original PRG prefix. `BinaryObliviousMatrix.lean` and
`BinaryMultitapeMatrix.lean` connect both binary constructions to the actual
fixed-address program and efficient multitape source computation, with
derived `O(T log T)` binary payload length and arbitrary-prior privacy.

`SeedBudget.lean` chooses `c` strictly between source exponent `k` and PRG
stretch exponent `c₀`, proves `0 < k/c < 1`, and constructs the rounded seed
`ceil(C (N+1)^(k/c))`. Its sufficient pad capacity, sublinear power bound,
and polynomial resource bound are proved, including integer rounding.
`PRGRestriction.lean` derives exact-prefix security by free circuit wiring.
`PRGReindex.lean` derives input-indexed security from seed-indexed security.
Rounding need not be injective: the reduction selects a maximally
distinguishing circuit from each finite fiber, bounds its size using the
proved polynomial inverse of the chosen seed length, and proves preservation
of negligible advantage.
`PrivatePolynomialTime.lean` retains the sharp source exponent in the
`O(N^k log N)` event bound, derives the full power-stretch budget, and proves
privacy for the actual encrypted binary matrix using this chosen seed.
Its external cryptographic premise is the original seed-indexed PRG security,
not security of a stronger specially reindexed family. `output_at_source_time`
proves padding preserves the halted source answer, and `context_bound` gives
the actual native model's `O(N^k log N)` context bound. `no_readability_full_word`
also permits an arbitrary fixed encoding of all actual visible tokens and
the generated separator.

`ProtocolMatrix.lean` inserts a greedy-generated separator into a causal
schedule and shifts later source addresses, proving preservation of every
output-suffix event. `ProtocolEncryptedBinary.lean` generates the binary
ciphertext, separator, and plaintext answer with one shared numerical model.
`ProtocolMultitapeMatrix.lean` connects that complete Boolean protocol to the
efficient multitape compiler; its initializer is a depth-one raw literal
circuit. Its first-separator model also satisfies the checked seeded parity
footprint bound. `MultitapeOutputMatrix.lean` proves read-only suffix execution
preserves final memory and reads every requested source output bit through
an actual generated token's Boolean label. The modules described next close
the encrypted whole-output and first-EOS construction gaps.

`ProtocolSerialization.lean` derives the circuit reduction for any fixed
encoding of the entire native visible word, including its separator. Its
depth is at most three and its gate count is at most five times the encoded
word length. Thus privacy is not limited to an extracted token projection,
and the final plaintext answer remains outside the monitored reasoning word.

`CausalToken.lean` connects the native growing-prefix driver to the full-token
fiber and source-coding proofs. `TokenSymbolic.lean` preserves prefix
restriction when slicing full-uniform alphabets, and `SeededToken.lean`
preserves it when fixing private seed wires. `ProtocolToken.lean` applies
these lower bounds to the same complete native encrypted protocol, rather
than to an unrelated fixed-context generator.

`ReadoutSchedule.lean` appends public readouts without altering the original
causal prefix. `ScheduleRelabel.lean` proves preservation under alphabet
embeddings. `EncryptedReadout.lean` and `EncryptedFiniteReadout.lean` turn
encrypted event blocks into native plaintext output bits or full finite
symbols using static local PRG neighborhoods and finite decoder opcodes.
They preserve the binary ciphertext prefix exactly and derive whole-word
privacy without assuming security of a duplicated-pad generator.

`EncryptedMultitapeOutput.lean` and `EncryptedMultitapeFiniteOutput.lean`
instantiate these readouts on actual final simulator memory. Their raw-bit
and raw-seed initializers are depth-one literal circuits.
`DelimitedWord.lean` proves first-EOS decoding, including empty answers.
`PrivateOutput.lean` and `PrivateWordOutput.lean` derive the seed, security,
context, dimension, and parameter bounds for these actual models.
`MultitapeOutputCapacity.lean` proves that unit-motion source machines cannot
write beyond their time horizon. `PolynomialWordOutput.lean` uses this to
derive the output capacity `N+T+1`, removing any extra output-length premise.
Its source premises are just ordinary runtime, terminal-state, and output
representation correctness statements for the function being computed.

`FoldProgram.lean` constructs an actual fixed-address, constant-finite-state
fold. `ElementaryTaskUpper.lean` proves parity, full `S₅` product, and positive
alphabet addition correctness. `EncryptedFold.lean` derives linear context,
sublinear seed allocation, native output/EOS, and arbitrary-prior privacy on
the complete input alphabets. `EncryptedTaskUpper.lean` supplies the three
concrete task instances and proves linear dimension/quadratic parameter
bounds. `PositiveAdditionFootprint.lean` gives the matching full-uniform
addition lower bound for values `symbol.val+1`, not only the older zero-based
encoding. `FiniteProtocolPrivacy.lean` extends the whole-word reductions to
arbitrary nonempty finite input families.

`LogSquaredSeedBudget.lean` absorbs the log-squared overhead into a strictly
positive exponent margin. `NearLinearPrivateBit.lean` derives the actual
encrypted source model, native answer/EOS, security reindexing, near-linear
context, fixed heads/precision, and polynomial resources using only stretch
greater than one. The optional older
`PrivateMultiplication.encrypted_upper_bound` interface instantiates it from
an `N log N` multiplication premise, proves the actual generated middle-bit
and EOS tokens, and retains the sublinear-seed and `O(N log² N)` context
bounds. The current `VerifiedMultiplication.complete` construction instead
proves its multiplier locally and has `O(N log³ N)` context.

`ScheduleRecoding.lean` proves public-position vocabulary quotients.
`ExactEncryptedAlphabet.lean` derives source recovery, compiles the quotient
into native shared numerical matrices, proves raw literal initialization,
and transports whole-prefix privacy with its separator. `ExactTaskAlphabet.lean`
provides the concrete task alphabets and checks the `S₅` cardinality.
`CausalBoundary.lean` and `CausalSymbolicToken.lean` identify the actual first
separator even when several answer/EOS events follow it.
`CausalSymbolicFootprint.lean` relates the entropy of that first-separator
transcript to the actual full native prefix. `ExactFoldPrompt.lean` checks
single-raw-symbol wiring on the full task alphabets; `ExactFoldTrace.lean`
derives the seeded MI and expected-length bounds. `ExactFoldTheorem.lean`
assembles the three complete same-model elementary task statements.
`ExactMultitapeOutput.lean`, `ExactBinaryWord.lean`, `ExactNearLinear.lean`,
`ExactNearLinearTrace.lean`, and `ExactMultiplication.lean` provide the exact
four-token source-output and multiplication interfaces. No precomputed
reasoning or answer is an initializer input.
`PlainBinaryWord.lean` uses an explicitly constructed zero pad and an empty
seed to expose the unconditional whole-word simulation separately from
the cryptographic results; it imports no PRG existence or security premise.

`LookupTransformer.lean` additionally constructs a literal matrix-level,
zero-layer fixed-precision Transformer for every Boolean map on a finite type.
It classifies already packed finite-domain inputs; `ObliviousSimulation`
records the resulting bitwise lookup theorem without storing a realization
certificate in the transition interface. This does not assemble the
multiple attended values and local transition into the required numerical
one-layer matrix Transformer:

- `LookupTransformer.run_oneHot`
- `LookupTransformer.run_ofFiniteFunction`
- `LookupTransformer.finiteMap_bits_realized`
- `ObliviousSimulation.machineLocalMLP_bits_realized`

Finally, `LocalUnrecoverability.lean` formalizes both FAQ propositions against
unrestricted observers at the finite information-theoretic level.
Adjacent-pair parities reveal exactly `N/2` information bits; the general
complement construction, with its orbit identifier included, reveals exactly
`N-1`. Every individual bit stays exactly chance-predictable, and the private
pivot chooses the correct final answer. Efficient machine/matrix packaging
of these FAQ examples is not part of the requested completion scope:

- `LocalUnrecoverability.no_individual_bit_recoverable`
- `LocalUnrecoverability.invariant_under_complement_no_bit_recoverable`
- `LocalUnrecoverability.symmetricTrace_no_individual_bit_recoverable`
- `LocalUnrecoverability.pairedTrace_information`
- `LocalUnrecoverability.canonicalSymmetricTrace_information`
- `LocalUnrecoverability.canonicalSymmetricTrace_no_bit_recoverable`
- `LocalUnrecoverability.canonicalSymmetricTrace_output`

`Verification.lean` is a build-time kernel dependency audit of the headline
results. It rejects `sorryAx` and every axiom other than Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`. It includes the complete local
Tal proof and its original `216^d` statement, as well as the locally proved
multiplier and both replacement headline theorems. PRG security is the only
research argument of the current encrypted core results; the seed-free
headline has none. Fast multitape
multiplication is an explicit argument only of the optional older sharp-bound
interfaces.
The audit includes the complete exact-alphabet task statements, their
native-prefix bridges, raw initializers, and whole-output compiler.

There are no explicit proof placeholders and no number-theoretic character-sum
machinery: in particular, the proof does not use Dirichlet characters,
conductors, Pólya--Vinogradov, unit-group Hankel matrices, or carry-block
recurrences.

Build with:

```sh
lake build
```
