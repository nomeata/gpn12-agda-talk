\section{Der optimale Spieler}

\begin{comment}
\begin{code}
module Pebbels5 where

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
  pick : (n : ℕ) → suc n < 7 → Move

picked : Move → ℕ
picked (pick n _) = suc n

Strategy = ℕ → Move

evenList : {A : Set} → List A → Bool
evenList [] = true
evenList (_ ∷ xs) = not (evenList xs)

play : (m n : ℕ) → n < m → Strategy → Strategy → List ℕ 
play 0 _ () _ _
play (suc m) 0 _ _ _ = []
play (suc m) (suc n) (s≤s n<m) p1 p2 with p1 (suc n)
... | pick k _ = suc n ∷ play m (suc n ∸ suc k) n-k<m p2 p1
  where n-k<m = start n ∸ k <⟨ s≤s (n∸m≤n k n) ⟩ n <⟨ n<m ⟩ m □

player1 : Strategy
player1 _ = pick 0 (s≤s (s≤s z≤n))
player2 : Strategy
player2 _ = pick 1 (s≤s (s≤s (s≤s z≤n)))
\end{code}
\end{comment}

Zum Abschluss möchten wir jetzt noch einen besseren Spieler implementieren, nämlich einen, der die optimale Strategie fährt:

\begin{quote}
Nimm immer so viele Murmeln, dass danach eine mehr als ein Vielfaches von 7 liegen bleigen.
\end{quote}

Das geht immer, es sei denn, es liegt bereits eine mehr als ein Vielfaches von 7 Murmeln auf dem Tisch. Wenn wir also z.B. mit 100 Murmeln beginnen und der erste Spieler diese Strategie fährt, gewinnt er auf jeden Fall.

Implementieren wir also diesen Spieler. Der Ausdruck \li-k mod 7- gibt einen Wert vom Typ \li-Fin 7- zurück; das sind natürliche Zahlen kleiner als 7. (Wir hätten also \li-Fin 6- auch selbst für \li-Move- verwenden können; aber so wars lehrreicher). Die Funktion \li-toℕ- macht daraus wieder eine normale natürliche Zahl, während \li-bounded r- den Beweis \li-toℕ 7 < 7- liefert.
\begin{code}
opt : Strategy
opt k with pred k mod 7
... | zero    = pick 0 (s≤s (s≤s z≤n))
... | (suc r) = pick (toℕ r) (s≤s (bounded r)) 
\end{code}

\begin{comment}
\begin{code}
winner : ℕ → Strategy → Strategy → Bool
winner n p1 p2 = evenList (play (suc n) n ≤-refl p1 p2)
\end{code}
\end{comment}

Nun wollen wir beweisen, dass die optimale Strategie wirklich die optimale ist. Wie würde wohl so ein Lemma aussehen? Vermutlich so, wobei \li-1'- eine eins vom Typ \li-Fin 7- ist.
\begin{code}
opt-is-opt : ∀ n s → n mod 7 ≢ 1' → winner n opt s ≡ true
\end{code}

Aber um dort anzukommen brauchen wir ein paar Hilfslemmas, die sich an der Struktur von \li-play- orientieren.
\begin{code}
opt-is-opt1 : ∀ m n n<m s → n mod 7 ≢ 1' → evenList (play m n n<m opt s) ≡ true
opt-is-opt2 : ∀ m n n<m s → n mod 7 ≡ 1' → evenList (play m n n<m s opt) ≡ false
\end{code}

Beginnen wir mit dem zweiten Fall. Generell kommt man beim Beweisen am besten voran, wenn man die Struktur des Programms, über das man den Beweis führt, nachvollzieht. Den Beweis von n-k<m müssen wir zum Glück nicht kopieren, da der schon in \li-play- gegeben ist und dem Typ-Checker klar ist, dass wir den und nur genau den hier verwenden müssen.

\begin{code}
opt-is-opt2 0 _ () _ _
opt-is-opt2 _ 0 _ _ ()
opt-is-opt2 (suc m) (suc n) (s≤s n<m) s eq with s (suc n)
opt-is-opt2 (suc m) (suc n) (s≤s n<m) s eq | pick k k<7 = cong not $
  opt-is-opt1 m (n ∸ k) _ s (lem-sub-p n k eq k<7)
\end{code}

Das Lemma \li!lem-sub-p! habe ich bereits vorbereitet (Modul \li-DivModUtils-):
\begin{lstlisting}
lem-sub-p : ∀ n p → (suc n mod 7 ≡ suc zero) → suc p < 7 → ((suc n ∸ suc p) mod 7 ≢ (suc zero))
\end{lstlisting}

Nun zum Beweis des zweiten Falls. Der wird sehr ähnlich aussehen, wieder brauchen wir ein Lemma analog zu dem bereits vorbereiteten, diesmal für \li-opt-. Das sieht dann so aus:

\begin{code}
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
\end{code}

Der zweite Fall sieht wiederum dem ersten Fall ähnlich. Entscheident ist, wo wir das \li!lem-opt! einbauen: Nach dem Aufruf von \li-with opt (suc n)- wird der Zusammenhang zwischen \li-pick k k<7- und \li-opt (suc n)- vergessen sein, den brauchen wir allerdings um \li!lem-opt! anwenden zu können. Daher müssen wir auf beides \emph{gleichzeitig} matchen.

\begin{code}
opt-is-opt1 0 _ () _ _
opt-is-opt1 (suc m) 0 _ _ _ = refl
opt-is-opt1 (suc m) (suc n) (s≤s n<m) s neq with opt (suc n) | lem-opt n neq
opt-is-opt1 (suc m) (suc n) (s≤s n<m) s neq | pick k k<7 | eq = cong not $
  opt-is-opt2 m (n ∸ k) _ s eq 
\end{code}

Und nun ist der Beweis, dass unsere Strategie immer gewinnt, einfach:
\begin{code}
opt-is-opt n = opt-is-opt1 (suc n) n ≤-refl
\end{code}

