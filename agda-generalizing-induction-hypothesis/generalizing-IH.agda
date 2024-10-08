{-
-- This agda module contains several classical exercises on generalizing a induction hypothesis.
--
-- credit: thanks James Wilcox for collecting these exercises
-- upper stream source: https://jamesrwilcox.com/InductionExercises.html
-}


open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.List
open import Data.List.Properties

sum-tail' : List ℕ → ℕ → ℕ
sum-tail' [] acc = acc
sum-tail' (x ∷ xs) acc = sum-tail' xs (acc + x)

sum-tail : List ℕ → ℕ
sum-tail xs = sum-tail' xs 0

sum-tail-lemma : ∀ (z : ℕ) (xs : List ℕ) → sum-tail' xs z ≡ z + sum xs
sum-tail-lemma z [] rewrite +-identityʳ z = refl
sum-tail-lemma z (x ∷ xs) rewrite sum-tail-lemma (z + x) xs | +-assoc z x (sum xs) = refl

sum-tail-correct : ∀ (xs : List ℕ) → sum xs ≡ sum-tail xs
sum-tail-correct xs rewrite sum-tail-lemma 0 xs = refl


sum-cont' : ∀ {A : Set} (xs : List ℕ) (k : ℕ → A) → A
sum-cont' [] k = k 0
sum-cont' (x ∷ xs) k = sum-cont' xs (λ s → k (x + s))

sum-cont : List ℕ → ℕ
sum-cont xs = sum-cont' xs (λ x → x)

sum-cont-lemma : ∀ {A : Set} (k : ℕ → A) (xs : List ℕ) → sum-cont' xs k ≡ k (sum xs)
sum-cont-lemma k [] = refl
sum-cont-lemma k (x ∷ xs) rewrite sum-cont-lemma (λ s → k (x + s)) xs = refl

sum-cont-correct : ∀ (xs : List ℕ) → sum xs ≡ sum-cont xs
sum-cont-correct xs rewrite sum-cont-lemma (λ s → s) xs = refl



data Expr : Set where
  Const : ℕ → Expr
  Plus : Expr → Expr → Expr

eval-expr : Expr → ℕ
eval-expr (Const n) = n
eval-expr (Plus e1 e2) = eval-expr e1 + eval-expr e2

eval-expr-tail' : Expr → ℕ → ℕ
eval-expr-tail' (Const n) acc = acc + n
eval-expr-tail' (Plus e1 e2) acc = eval-expr-tail' e2 (eval-expr-tail' e1 acc)

eval-expr-tail : Expr → ℕ
eval-expr-tail e = eval-expr-tail' e 0

eval-tail-lemma : ∀ (e : Expr) (n : ℕ) → eval-expr-tail' e n ≡ n + eval-expr e
eval-tail-lemma (Const x) n = refl
eval-tail-lemma (Plus e1 e2) n rewrite eval-tail-lemma e1 n 
                                     | eval-tail-lemma e2 (n + eval-expr e1) 
                                     | +-assoc n (eval-expr e1) (eval-expr e2)
                                     = refl

eval-tail-correct : ∀ (e : Expr) → eval-expr-tail e ≡ eval-expr e
eval-tail-correct e rewrite eval-tail-lemma e 0 = refl

eval-expr-cont' : ∀ {A : Set} → Expr → (ℕ → A) → A
eval-expr-cont' (Const n) k = k n
eval-expr-cont' (Plus e1 e2) k = eval-expr-cont' e1 λ { r1 →
                                   eval-expr-cont' e2 λ { r2 →
                                     k (r1 + r2) } }
eval-expr-cont : Expr → ℕ
eval-expr-cont e = eval-expr-cont' e λ { x → x }

eval-cont-lemma : ∀ {A : Set} (k : ℕ → A) (e : Expr) → eval-expr-cont' e k ≡ k (eval-expr e)
eval-cont-lemma k (Const x) = refl
eval-cont-lemma k (Plus e1 e2) rewrite eval-cont-lemma (λ r1 → eval-expr-cont' e2 (λ r2 → k (r1 + r2))) e1 
                                     | eval-cont-lemma (λ r2 → k (eval-expr e1 + r2)) e2
                                     = refl

eval-cont-correct : ∀ (e : Expr) → eval-expr-cont e ≡ eval-expr e
eval-cont-correct e rewrite eval-cont-lemma (λ n → n) e = refl



fib : ℕ → ℕ
fib zero = 1
fib (suc zero) = 1
fib (suc (suc n)) = fib (suc n) + fib n

fib-tail : ℕ → ℕ → ℕ → ℕ
fib-tail zero a b = b
fib-tail (suc n) a b = fib-tail n (a + b) a


fib-helper : ∀ (n m a b : ℕ) → a ≡ fib (suc m) → b ≡ fib m → fib-tail n a b ≡ fib (n + m)
fib-helper zero m .(fib (suc m)) .(fib m) refl refl = refl
fib-helper (suc n) m .(fib (suc m)) .(fib m) refl refl 
  rewrite fib-helper n (suc m) (fib (suc m) + fib m) (fib (suc m)) refl refl 
        | sym (+-assoc n 1 m) 
        | +-comm n 1 = refl

-- n     0 1 2 3 4 5
-- fib n 1 1 2 3 5 8
--
-- fib-tail 4 1 1    0 = fib 0
-- fib-tail 3 2 1    1 = fib 1
-- fib-tail 2 3 2    2 = fib 2
-- fib-tail 1 5 3    3 = fib 3
-- fib-tail 0 8 5 =  5 = fib 4

fib-correct : ∀ (n : ℕ) → fib n ≡ fib-tail n 1 1
fib-correct n rewrite fib-helper n 0 1 1 refl refl
                      | +-identityʳ n
                      = refl




data Instruction : Set where
  Push : ℕ → Instruction
  Add  :     Instruction

Program Stack : Set
Program = List Instruction
Stack   = List ℕ

run : Program → Stack → Stack
run [] s = s
run (Push n ∷ p) s = run p (n ∷ s)
run (Add ∷ p) [] = run p []
run (Add ∷ p) (x ∷ []) = run p [ x ]
run (Add ∷ p) (x ∷ y ∷ s) = run p (y + x ∷ s)

compile : Expr → Program
compile (Const x) = [ Push x ]
compile (Plus e1 e2) = compile e1 ++ compile e2 ++ [ Add ]

run-concat : ∀ (p q : Program) (s : Stack)
  → run (p ++ q) s ≡ run q (run p s)
run-concat [] q s = refl
run-concat (Push x ∷ p) q s = run-concat p q (x ∷ s)
run-concat (Add ∷ p) q [] = run-concat p q []
run-concat (Add ∷ p) q (x ∷ []) = run-concat p q [ x ]
run-concat (Add ∷ p) q (x1 ∷ x2 ∷ s) = run-concat p q ((x2 + x1) ∷ s)



run-lemma : ∀ (e : Expr) (p : Program) (s : Stack)
  → run (compile e ++ p) s ≡ run p (eval-expr e ∷ s)
run-lemma (Const x) p s = refl
run-lemma (Plus e1 e2) p s
  rewrite ++-assoc (compile e1) (compile e2 ++ [ Add ]) p
        | run-concat (compile e1) ((compile e2 ++ [ Add ]) ++ p) s
        | sym (++-identityʳ (compile e1)) | run-lemma e1 [] s
        | ++-assoc (compile e2) [ Add ] p
        | run-concat (compile e2) (Add ∷ p) (eval-expr e1 ∷ s)
        | sym (++-identityʳ (compile e2)) | run-lemma e2 [] (eval-expr e1 ∷ s)
  = refl

-- execution trace
-- < [compile e1 ; compile e2 ; Add] , [] >
-- < [compile e2 ; Add] , [ eval e1 ] >
-- < [Add] ; [ eval e2 ; eval e1 ] >
-- < [] ; [ eval (e1 + e2) ] >

compile-correct : ∀ (e : Expr) → (eval-expr e) ∷ [] ≡ run (compile e) []
compile-correct e rewrite sym (run-lemma e [] []) 
                        | ++-identityʳ (compile e)
                        = refl

