import .love01_definitions_and_statements_demo


/-! # LoVe Homework 1: Definitions and Statements

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (1 point): Fibonacci Numbers

1.1 (1 point). Define the function `fib` that computes the Fibonacci
numbers. -/

def fib : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n + 2) := fib n + fib (n + 1)
-- My first, incorrect try! Fails with "failed to prove recursive application is decreasing, well founded relation"
-- | (n + 2) := fib (n - 1) + fib (n - 2)

/-! 1.2 (0 points). Check that your function works as expected. -/

-- If you forget to specify that = β is decidable, you get this error:
-- failed to synthesize type class instance for... ⊢ decidable (f a = b)
meta def test_unary_op {α β} [has_to_format α] [has_to_format β] [decidable_eq β]
  (name : string) (f : α → β) (test_data : list (α × β)) : tactic unit :=
test_data.mmap' (λ ⟨a, b⟩,
  guard (f a = b) <|> tactic.fail format!"{name} {a} wasn't {b}, it was {f a}")

#eval test_unary_op "fib" fib
  [(0, 0), (1, 1), (2, 1), (3, 2), (4,3), (5,5), (6,8), (7,13), (8,21)]

/-! ## Question 2 (3 points): Lists

Consider the type `list` described in the lecture and the `append₂` and
`reverse` functions from the lecture's demo. The `list` type is part of Lean's
core libraries. You will find the definition of `append₂` and `reverse` in
`love01_definitions_and_statements_demo.lean`. One way to find them quickly is
to

1. hold the Control (on Linux and Windows) or Command (on macOS) key pressed;
2. move the cursor to the identifier `list`, `append₂`, or `reverse`;
3. click the identifier. -/

#print list
#check append₂
#check reverse

/-! 2.1 (1 point). Test that `reverse` behaves as expected on a few examples.

In the first example, the type annotation `: list ℕ` is needed to guide Lean's
type inference. -/

#eval test_unary_op "reverse" reverse
  [(([] : list ℕ), []), ([1,2,3], [3,2,1])]

-- For now, need separate tests for separate list types. Don't know how to generify the original code.
#eval test_unary_op "reverse" reverse
  [(([] : list string), []), (["h","e","l","l","o"],["o", "l","l","e","h"])]

/-! 2.2 (2 points). State (without proving them) the following properties of
`append₂` and `reverse`. Schematically:

    `append₂ (append₂ xs ys) zs = append₂ xs (append₂ ys zs)`
    `reverse (append₂ xs ys) = append₂ (reverse ys) (reverse xs)`

for all lists `xs`, `ys`, `zs`. Try to give meaningful names to your lemmas. If
you wonder how to enter the symbol `₂`, have a look at the table at the end of
the preface in the Hitchhiker's Guide.

Hint: Take a look at `reverse_reverse` from the demonstration file. -/

#check sorry_lemmas.reverse_reverse

-- enter your lemma statements here

lemma append₂_communicative : ∀ {α : Type} (xs : list α) (ys: list α) (zs : list α),
    append₂ (append₂ xs ys) zs = append₂ xs (append₂ ys zs) :=
    sorry

lemma reverse_append₂ : ∀ {α : Type} (xs : list α) (ys: list α),
    reverse (append₂ xs ys) = append₂ (reverse ys) (reverse xs) :=
    sorry

#check append₂_communicative
#check reverse_append₂

/-! ## Question 3 (5 points): λ-Terms

3.1 (2 points). Complete the following definitions, by replacing the `sorry`
placeholders by terms of the expected type.

Please use reasonable names for the bound variables, e.g., `a : α`, `b : β`,
`c : γ`.

Hint: A procedure for doing so systematically is described in Section 1.1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def B : (α → β) → (γ → α) → γ → β :=
λ f g c, f (g c)

def S : (α → β → γ) → (α → β) → α → γ :=
λ f g a, f a (g a)

def more_nonsense : (γ → (α → β) → α) → γ → β → α :=
λ f g b, f g (λx,b)

def even_more_nonsense : (α → α → β) → (β → γ) → α → β → γ :=
λf g a b, g b

/-! 3.2 (1 point). Complete the following definition.

This one looks more difficult, but it should be fairly straightforward if you
follow the procedure described in the Hitchhiker's Guide.

Note: Peirce is pronounced like the English word "purse". -/

def weak_peirce : ((((α → β) → α) → α) → β) → β :=
λf, f (λg, g (λa, f (λh, a)))

/-! 3.3 (2 points). Show the typing derivation for your definition of `S` above,
using ASCII or Unicode art. You might find the characters `–` (to draw
horizontal bars) and `⊢` useful.

Feel free to introduce abbreviations to avoid repeating large contexts `C`. -/

-- write your solution here

/-!
def S : (α → β → γ) → (α → β) → α → γ :=
λ f g a, f a (g a)

Define local context C to have f: (α → β → γ), g: (α → β), a: α.
Start by typing these using the Var rule:

------------------ Var -------------- Var
C ⊢ f: (α → β → γ)     C ⊢ g: (α → β)

Next, type the applications one parameter at a time:

---------------------------- App ----------- App ---- Var
C ⊢ f a : (β → γ)                C ⊢ g a : β     a: α
--------------------------------------------------------- App
C ⊢ f a (g a) : γ

Finally, add the lambda parameters one at a time:

----------------------------------------------------------------------------------- Lam
f: (α → β → γ), g: (α → β) ⊢λ f g (a: α), f a (g a) : (α → β → γ) → (α → β) → α → γ
----------------------------------------------------------------------------------- Lam
f: (α → β → γ) ⊢λ f (g: (α → β)) (a: α), f a (g a) : (α → β → γ) → (α → β) → α → γ
---------------------------------------------------------------------------------- Lam
λ (f: (α → β → γ)) (g: (α → β)) (a: α), f a (g a) : (α → β → γ) → (α → β) → α → γ
-/

end LoVe
