import .love01_definitions_and_statements_demo


/-! # LoVe Exercise 1: Definitions and Statements

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1: Truncated Subtraction

1.1. Define the function `sub` that implements truncated subtraction on natural
numbers by recursion. "Truncated" means that results that mathematically would
be negative are represented by 0. For example:

    `sub 7 2 = 5`
    `sub 2 7 = 0` -/

def sub : ℕ → ℕ → ℕ
| m 0 := m
| 0 n := 0
| (nat.succ m) (nat.succ n) := sub m n

/-! 1.2. Check that your function works as expected. -/

#check ∀ m n : ℕ, n ≤ m ∧ sub m n = m - n ∨ m ≤ n ∧ sub m n = 0

-- lemma sub_works_properly: ∀ m n : ℕ, n ≤ m ∧ sub m n = m - n ∨ m ≤ n ∧ sub m n = 0 :=
-- begin
-- intros m n
-- sorry
-- end

namespace sub_tests

-- Tuples are defined here: https://leanprover-community.github.io/mathlib_docs/init/core.html#prod.mk

-- Thanks to Mario Carneiro for the following code; if you use "def" instead of "meta def", you get the
-- error "invalid definition, it uses untrusted declaration 'has_to_format'"
-- Note also that using `lemma` with `refl` is the way to use the verified kernel; #eval uses the much more
-- efficient interpreter which is not verified.
meta def test_binop {α β γ} [has_to_format α] [has_to_format β] [has_to_format γ] [decidable_eq γ]
  (name : string) (f : α → β → γ) (test_data : list (α × β × γ)) : tactic unit :=
test_data.mmap' (λ ⟨a, b, c⟩,
  guard (f a b = c) <|> tactic.fail format!"{name} {a} {b} wasn't {c}, it was {f a b}")

#eval test_binop "sub" sub
  [(0, 0, 0), (0, 1, 0), (0, 7, 0), (1, 0, 1), (1, 1, 0), (3, 0, 3),
   (2, 7, 0), (3, 1, 2), (3, 3, 0), (3, 7, 0), (7, 2, 5)]

-- Previous attempts at testing:

-- Non-reusable logic and uses syntax I don't know. What does "show tactic unit, from" mean?
-- def sub_test_data : list (ℕ × ℕ × ℕ) :=
-- [(0, 0, 0), (0, 1, 0), (0, 7, 0), (1, 0, 1), (1, 1, 0), (3, 0, 3),
--  (2, 7, 0), (3, 1, 2), (3, 3, 0), (3, 7, 0), (7, 2, 5)]

-- #eval show tactic unit, from
--   sub_test_data.mmap' (λ ⟨a, b, c⟩,
--     guard (sub a b = c) <|> tactic.fail format!"sub {a} {b} wasn't {c}, it was {sub a b}")

-- properly fails with wrong output, but still has to be repeated for every test case
#eval (guard (sub 0 0 = 0): tactic unit)

-- Uses verified kernel, but still has to be repeated for every test case
-- lemma test_sub00: sub 0 0 = 0 := rfl

-- dumbest/simplest way- you have to check the output manually
-- #eval sub 0 0   -- expected: 0
-- #eval sub 0 1   -- expected: 0
-- #eval sub 0 7   -- expected: 0
-- #eval sub 1 0   -- expected: 1
-- #eval sub 1 1   -- expected: 0
-- #eval sub 3 0   -- expected: 3
-- #eval sub 2 7   -- expected: 0
-- #eval sub 3 1   -- expected: 2
-- #eval sub 3 3   -- expected: 0
-- #eval sub 3 7   -- expected: 0
-- #eval sub 7 2   -- expected: 5

end sub_tests

/-! ## Question 2: Arithmetic Expressions

Consider the type `aexp` from the lecture and the function `eval` that
computes the value of an expression. You will find the definitions in the file
`love01_definitions_and_statements_demo.lean`. One way to find them quickly is
to

1. hold the Control (on Linux and Windows) or Command (on macOS) key pressed;
2. move the cursor to the identifier `aexp` or `eval`;
3. click the identifier. -/

#check aexp
#check eval

/-! 2.1. Test that `eval` behaves as expected. Make sure to exercise each
constructor at least once. You can use the following environment in your tests.
What happens if you divide by zero?

Make sure to use `#eval`. For technical reasons, `#reduce` does not work well
here. Note that `#eval` (Lean's evaluation command) and `eval` (our evaluation
function on `aexp`) are unrelated. -/

def some_env : string → ℤ
| "x" := 3
| "y" := 17
| _   := 201

#eval eval some_env (aexp.var "x")   -- expected: 3

#eval eval some_env (aexp.add (aexp.num 1) (aexp.num 5)) -- expected: 6
#eval eval some_env (aexp.sub (aexp.var "y") (aexp.var "x")) -- expected: 14
#eval eval some_env (aexp.mul (aexp.num 2) (aexp.var "z")) -- expected: 402
#eval eval some_env (aexp.div (aexp.var "z") (aexp.num 2)) -- expected: 100
-- invoke `#eval` here

/-! 2.2. The following function simplifies arithmetic expressions involving
addition. It simplifies `0 + e` and `e + 0` to `e`. Complete the definition so
that it also simplifies expressions involving the other three binary
operators. -/

def simplify : aexp → aexp
| (aexp.add (aexp.num 0) e₂) := simplify e₂
| (aexp.add e₁ (aexp.num 0)) := simplify e₁
-- insert the missing cases here
| (aexp.sub e₁ (aexp.num 0)) := simplify e₁
| (aexp.mul (aexp.num 0) e₂) := (aexp.num 0)
| (aexp.mul e₁ (aexp.num 0)) := (aexp.num 0)
| (aexp.mul (aexp.num 1) e₂) := simplify e₂
| (aexp.mul e₁ (aexp.num 1)) := simplify e₁
| (aexp.div e₁ (aexp.num 0)) := (aexp.num 0)
| (aexp.div (aexp.num 0) e₂) := (aexp.num 0)
| (aexp.div e₁ (aexp.num 1)) := simplify e₁
| (aexp.div (aexp.num 1) e₂) := simplify e₂
-- catch-all cases below
| (aexp.num i)               := aexp.num i
| (aexp.var x)               := aexp.var x
| (aexp.add e₁ e₂)           := aexp.add (simplify e₁) (simplify e₂)
| (aexp.sub e₁ e₂)           := aexp.sub (simplify e₁) (simplify e₂)
| (aexp.mul e₁ e₂)           := aexp.mul (simplify e₁) (simplify e₂)
| (aexp.div e₁ e₂)           := aexp.div (simplify e₁) (simplify e₂)

/-! 2.3. Is the `simplify` function correct? In fact, what would it mean for it
to be correct or not? Intuitively, for `simplify` to be correct, it must
return an arithmetic expression that yields the same numeric value when
evaluated as the original expression.

Given an environment `env` and an expression `e`, state (without proving it)
the property that the value of `e` after simplification is the same as the
value of `e` before. -/

lemma simplify_correct (env : string → ℤ) (e : aexp) :
  eval env e = eval env (simplify e) :=   -- replace `true` by your lemma statement
sorry


/-! ## Question 3: λ-Terms

3.1. Complete the following definitions, by replacing the `sorry` markers by
terms of the expected type.

Hint: A procedure for doing so systematically is described in Section 1.1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def I : α → α :=
λa, a

def K : α → β → α :=
λa b, a

/-!
Args define C to be f: (α → β → γ), a: α, b: β

We use the Var rule to assign types that exist in C already, then two
App applications to type the lambda body, f a b

—————————————————— Var  ————————— Var
C ⊢ f: (α → β → γ)      C ⊢ a: α
————————————————————————————————— App ———————— Var
C ⊢ f a : (β → γ)                     C ⊢ b: β
——————————————————————————————————————————————— App
C ⊢ f a b : γ

Now we use the Lam rule to create the final lambda definition, one parameter at a time

—————————————————————————————————————————— Lam
f: (α → β → γ), b: β ⊢ λ(a: α), f a b : (α → γ)
—————————————————————————————————————————————————————— Lam
f: (α → β → γ) ⊢ λ(b: β), λ(a: α), f a b : β → α → γ
—————————————————————————————————————————————————————— Lam
C ⊢ λ(f: (α → β → γ)) (b: β) (a: α), f a b : (α → β → γ) → β → α → γ
-/

def C : (α → β → γ) → β → α → γ :=
λf b a, f a b

def proj_1st : α → α → α :=
λ a b, a

/-! Please give a different answer than for `proj_1st`. -/

def proj_2nd : α → α → α :=
λ a b, b

def some_nonsense : (α → β → γ) → α → (α → γ) → β → γ :=
λ f a g b, f a b -- or g a

/-! 3.2. Show the typing derivation for your definition of `C` above, on paper
or using ASCII or Unicode art. You might find the characters `–` (to draw
horizontal bars) and `⊢` useful. -/

-- write your solution in a comment here or on paper

end LoVe
