/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55PWMain
public import ElboimSly.Paper.Escape.Es55MeasProof
public import ElboimSly.Paper.Escape.Es55DetProof
public import ElboimSly.Paper.Escape.Es55JumpProof
public import Mathlib

/-!
# ES22 Lemma 5.5

ES22 Lemma 5.5.  Assembly of the ingredients `es55DetAll`, `es55Jump`, `es55PW`,
`es55Meas`.
-/

@[expose] public section

namespace ElboimSly.Paper.Escape

/-- **ES22 Lemma 5.5** (ES22 Lemma 5.5). -/
theorem es5_5 {k : ℕ} (hk : 3 ≤ k) : Es55Concl k :=
  es5_5_of_ingredients hk (es55DetAll k) es55Jump es55PW es55Meas

end ElboimSly.Paper.Escape
