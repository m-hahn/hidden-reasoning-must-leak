/- Ported to the faithfulness project's pinned Lean/mathlib v4.19.0.
Upstream revision 311d27ad8458b61e9b7461fc83a480e4be97aef2; original copyright/license below. -/
/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Init

/-!
# Signatures and interpretations

A `Signature` specifies operation symbols with finite arities. The set of symbols
may be infinite, and their arities need not have a uniform bound.
An `Interpretation` assigns each symbol an operation on a carrier type.
Programs and circuits keep the signature separate from its interpretation.
-/
namespace Cslib.Circuits

universe v

/-- A collection of operation symbols, each with a fixed finite arity. -/
structure Signature where
  /-- The operation symbols of the signature. -/
  Op : Type v
  /-- The number of arguments taken by each operation symbol. -/
  Arity : Op → Nat

/-- An interpretation assigns an operation on `Carrier` to every symbol in `σ`. -/
abbrev Interpretation (σ : Signature) (Carrier : Type*) :=
  (op : σ.Op) → (Fin (σ.Arity op) → Carrier) → Carrier

end Cslib.Circuits
