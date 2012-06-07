\section{Termination}

Das hat im Vortrag leider keinen Platz mehr gehabt, aber der Vollständigkeit halber will ich hier noch darauf eingehen. Bisher waren die Funktion \li-play- und die Beweise, die darauf aufbauen, rot markiert. Damit zeigt Agda dass es nicht weiß ob \li-play- terminiert, also garantiert in keine Endlosschleife läuft. Warum ist das wichtig? Weil man mit Endlosschleifen beliebige Aussagen beweisen kann:
\begin{lstlisting}
unsinn : 42 < 7
unsinn = unsinn
\end{lstlisting}

Nun erkennt Agda in einfachen Fällen die Termination, etwa in der Funktion \li-evenList-. Hier ruft \li-evenList (x ∷ xs)- im rekursiven Fall \li-evenList xs- auf, das Argument ist also ein Teil des Parameters und Agda ist sich sicher dass diese Funktion irgendwann fertig ist.

Bei \li-play- ist das zwar auch der Fall, aber Agda sieht das nicht und wir müssen ihm auf die Sprünge helfen. Leider müssen wir diesen Beweis direkt in der Definition von \li-play- führen; das erfordert zusätzliche Parameter und damit größere Änderungen am Code und den Beweisen:

\begin{comment}
\begin{code}
module Pebbels6 where

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Nat.Divisibility
open import Data.Nat.DivMod
open import Relation.Nullary
open import Data.Nat.Properties
open import Data.Fin using (Fin; toℕ; zero; suc; fromℕ≤)
open import Data.Fin.Props
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product
open import Relation.Binary
open import Data.Empty
open import  Relation.Nullary.Negation
open ≡-Reasoning
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)
open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl; antisym to ≤-antisym)
import Algebra
open Algebra.CommutativeSemiring commutativeSemiring using (+-comm; +-assoc)


open import DivModUtils

data Move : Set where
  pick : (n : ℕ) → 0 < n → n < 7 → Move

picked : Move → ℕ 
picked (pick k _ _) = k

Strategy = ℕ → Move

evenList : {A : Set} → List A → Bool
evenList [] = true
evenList (_ ∷ xs) = not (evenList xs)

player1 : Strategy
player1 _ = pick 1 (s≤s z≤n) (s≤s (s≤s z≤n))
player2 : Strategy
player2 _ = pick 2 (s≤s z≤n)  (s≤s (s≤s (s≤s z≤n)))
opt : Strategy
opt k with pred k mod 7
... | zero = pick 1 (s≤s z≤n) (s≤s (s≤s z≤n))
... | (suc r) = pick (toℕ (suc r)) (s≤s z≤n) (s≤s (bounded r))
\end{code}
\end{comment}

\begin{code}
open import Induction.WellFounded 
open import Induction.Nat

play : (n : ℕ) → Acc _<_ n → Strategy → Strategy → List ℕ 
play 0 _ _ _ = []
play (suc n) (acc rec) p1 p2 with p1 (suc n)
... | pick 0 () _
... | pick (suc k) _ _ = (suc n) ∷ play (suc n ∸ suc k) (rec _ (s≤s (n∸m≤n k n))) p2 p1

winner : ℕ → Strategy → Strategy → Bool
winner n p1 p2 = evenList (play n (Subrelation.well-founded ≤⇒≤′ <-well-founded n) p1 p2)

opt-is-opt : ∀ n s → n mod 7 ≢ 1' → winner n opt s ≡ true

opt-is-opt1 : ∀ n a s → n mod 7 ≢ 1' → evenList (play n a opt s) ≡ true
opt-is-opt2 : ∀ n a s → n mod 7 ≡ 1' → evenList (play n a s opt) ≡ false

opt-is-opt2 0 _ _ ()
opt-is-opt2 (suc n) (acc a) s eq with s (suc n)
... | pick 0 () _
... | pick (suc k) 0<k k<7 = cong not $
  opt-is-opt1 (suc n ∸ suc k) _ s (lem-sub-p n (suc k) eq 0<k k<7)


lem-opt : ∀ n → suc n mod 7 ≢ 1' → (suc n ∸ picked (opt (suc n))) mod 7 ≡ 1'
lem-opt n neq with n divMod 7
lem-opt .(q * 7) neq | result q zero = ⊥-elim (neq (mod-lemma q 6 1'))
lem-opt .(1 + toℕ r + q * 7) neq | result q (suc r) = begin
  (1 + toℕ r + q * 7 ∸ toℕ r) mod 7
    ≡⟨ cong (λ y → (1 + y ∸ toℕ r) mod 7) $ +-comm (toℕ r) (q * 7) ⟩
  (1 + q * 7 + toℕ r ∸ toℕ r) mod 7
    ≡⟨ cong (λ y → y mod 7) $ m+n∸n≡m (1 + q * 7) (toℕ r) ⟩
  (1 + q * 7) mod 7
    ≡⟨ mod-lemma q 6 1' ⟩
  1' ∎

opt-is-opt1 0 _ _ _ = refl
opt-is-opt1 (suc n) (acc a) s neq with opt (suc n) | lem-opt n neq
... | pick 0 () _ | _
... | pick (suc k) 0<k k<7 | eq = cong not $
  opt-is-opt2 (suc n ∸ (suc k)) _ s eq

opt-is-opt n s = opt-is-opt1 n _ s

\end{code}

