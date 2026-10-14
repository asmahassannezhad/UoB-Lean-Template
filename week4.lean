/-
==========================================================================
  WEEK 4 — the slide examples, with explanations
  MATH30024 · Theme 3B · Mathematical Formalisation with Lean

  HOW TO USE THIS FILE
  1. Go to  https://live.lean-lang.org
  2. Select everything already in the editor and delete it.
  3. Paste this whole file in.
  4. Click on any line: the goal state appears in the panel on the right.

  Mathlib is already loaded on that site, so `import Mathlib` is fine here.
  In your own project, import only the parts you need — importing all of
  Mathlib is very slow.

  The web editor does NOT save your work. Keep your own copy.
==========================================================================
-/

import Mathlib

/-! ## 0. What Lean reads, and what it ignores

Everything between `/-` and `-/`, and everything after `--` on a line, is a
COMMENT. Lean ignores all of it. Most of this file is comment: the code is
only the lines that have none.

    -- a comment, to the end of the line
    /- a block comment, over several lines -/

LAYOUT MATTERS. Lean has no brackets or semicolons around a proof — it uses
indentation to see where the proof ends. Tactics after `by` must be indented,
and must line up with each other:

    example (n : ℕ) : n = n := by
      rfl        -- indented, so inside the proof

A tactic pushed back to the left margin ends the proof early, which produces
a confusing error. If something breaks for no visible reason, check the
indentation first. -/


/-! ## 1. Lean as a calculator

`#eval` computes a value. Put the cursor on the line and read the panel
on the right. -/

#eval 2 + 2
#eval "hello".length

-- Careful: subtraction on ℕ truncates at 0, it does not go negative.
#eval (3 : ℕ) - 10        -- 0, not -7

/-! ## 2. `#check` — what *is* this thing?

`#check` reports the *type* of an expression instead of its value. -/

#check 2 + 2              -- ℕ
#check Nat.add_comm


/-! ## 3. Reading a definition:  `:`  versus  `:=`

These two symbols look similar but mean different things.

  `:`   means "has type"        — read it as "is a"
  `:=`  means "is defined to be" — it introduces the body

So in

    def double (n : ℕ) : ℕ := 2 * n
        ^^^^^^  ^^^^^^^  ^^   ^^^^^
        name    input     |   body
                          result type

read: "double takes an n, which is a natural number, and produces a
natural number, defined to be 2 * n."

A `def` ASSERTS NOTHING, so there is nothing to prove.
A `theorem` / `lemma` / `example` STATES A CLAIM, so it needs a proof. -/

def double (n : ℕ) : ℕ := 2 * n

#eval double 7            -- 14
#check double             -- ℕ → ℕ


/-! ## 4. Stating and proving

Now a claim, so a proof is required. The proof comes after `:= by`. -/

theorem double_add (a b : ℕ) : double (a + b) = double a + double b := by
  unfold double           -- replace `double` by its definition
  ring                    -- finish the algebra


/-! ## 5. Logic

`exact` says: this is precisely the thing you were asked for. -/

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

-- `intro` introduces an assumption, exactly like "suppose P" on paper.
example (P Q : Prop) (hq : Q) : P → Q := by
  intro hp
  exact hq


/-! ## 6. Two tactics that finish goals for you

Ask yourself: is this step just algebra, or just linear bookkeeping?
If so, do not prove it by hand. -/

example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring                    -- identities in commutative rings

example (a b : ℝ) (h : a < b) : a + 1 < b + 1 := by
  linarith                -- linear arithmetic from the hypotheses

example (n : ℕ) (h : n > 3) : n ≥ 4 := by
  omega                   -- very good at arithmetic over ℕ and ℤ


/-! ## 7. Induction: the game versus real Lean

In the Natural Number Game you wrote

    induction n with d hd
    · rfl
    · rw [add_succ, hd]

Real Lean 4 wants NAMED CASES after `with`. This is why game code pasted
into this editor gives a syntax error. -/

example (n : ℕ) : 0 + n = n := by
  induction n with
  | zero      => rfl
  | succ d hd => rw [Nat.add_succ, hd]
  -- If `rw` complains it cannot find the pattern, use `simp [hd]` instead.


/-! ## 8. Real mathematics, written in Lean

A sequence IS a function ℕ → ℝ. So we write `u : ℕ → ℝ`, and the n-th term
is `u n` — juxtaposition, not a subscript.

`: Prop` says the result is a *proposition*: a statement that can be true
or false, not a number. -/

def SeqLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

#check SeqLimit

-- Read it aloud: "for all ε > 0 there exists N such that for all n ≥ N,
-- |uₙ - l| ≤ ε."  The notation is what you already write.


/-! ## 9. Stating an ∃ versus proving one

STATING an existential needs no witness — it is just a proposition.
PROVING one does: that is what `use` is for. -/

-- Stated, not proved (the `sorry` is the missing proof):
example : ∃ n : ℕ, n > 5 := by
  sorry

-- Proved, by supplying the witness:
example : ∃ n : ℕ, n > 5 := by
  use 6
  omega


/-! ## 10. Typing the symbols

Type the backslash abbreviation, then SPACE or TAB:

    \N    ℕ        \all   ∀        \le   ≤
    \R    ℝ        \ex    ∃        \ge   ≥
    \Z    ℤ        \and   ∧        \ne   ≠
    \to   →        \or    ∨        \in   ∈
    \eps  ε        \not   ¬        \iff  ↔

Hover over any symbol to see its abbreviation — that is how you look up
anything you meet in Mathlib. -/


/-! ## 11. YOUR TURN

Replace each `sorry`. A yellow warning on `sorry` is Lean telling you the
proof is unfinished — that is expected until you fill it in. -/

-- Hint: `ring`
example (x : ℝ) : (x + 1) * (x - 1) = x ^ 2 - 1 := by
  sorry

-- Hint: `omega`
example (n : ℕ) (h : n + 2 = 7) : n = 5 := by
  sorry

-- Hint: `intro`, then `exact`
example (P Q : Prop) (hp : P) : Q → P := by
  sorry

-- Hint: `unfold double`, then `ring`
example (n : ℕ) : double (n + 1) = double n + 2 := by
  sorry

/-
==========================================================================
  NEXT: A Glimpse of Lean — the four Introduction files.
  https://github.com/PatrickMassot/GlimpseOfLean
  (use the links under "Online version, no registration")
==========================================================================
-/
