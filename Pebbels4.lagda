\begin{comment}
\begin{code}
module Pebbels4 where

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
\end{code}
\end{comment}

\begin{comment}
\begin{code}
data Move : Set where
  pick : (n : ℕ) → suc n < 7 → Move

picked : Move → ℕ
picked (pick n _) = suc n

Strategy = ℕ → Move
\end{code}
\end{comment}

Agda erkennt die Termination von selber wenn eine Funktion per einfacher struktureller Induktion definiert ist. Wir haben schon so ein Beispiel, nämlich die Funktion \li-evenList-:
\begin{code}
evenList : {A : Set} → List A → Bool
evenList [] = true
evenList (_ ∷ xs) = not (evenList xs)
\end{code}
Diese Funktion ruft sich zwar auch selbst auf, aber immer mit einem Argument das ein Teil des ursprünglichen Arguments ist. Damit werden die Argumente immer kleiner (für einen sinnvollen Wert von klein) und die Termination ist sichergestellt. (Merke: Agda hat keine unendlichen Listen wie etwa Haskell!)

Nun wissen wir dass \li-play- höchstens so oft sich selbst aufruft, wie Murmeln auf dem Tisch liegen. Das nutzen wir aus um der Funktion einen Parameter zu verpassen, auf dem wir strukturell induzieren. Ein erster Versuch wäre z.B.

\begin{lstlisting}
play : ℕ → ℕ → Strategy → Strategy → List ℕ 
play 0 _ _ _ = []
play (suc m) 0 _ _ = []
play (suc m) n p1 p2 with p1 n
... | p = n ∷ play m (n ∸ picked p) p2 p1
\end{lstlisting}

Das funktioniert, ist aber unbefriedigend weil der erste Fall etwas künstlich ist; wir wissen dass der nicht vorkommt, wenn \li-m- groß genug, also möchten wir sichergehen dass \li-play- auch nur so verwendet wird. Wir fordern also vom Aufrufer, dass stets \li-n < m- gelte. Natürlich müssen wir das beim rekursiven Aufruf auch wieder beweisen, was ein paar Schritte benötigt. Für transitive Beweise gibt es eine nette Syntax, die uns erlaubt, zwischenschritte anzugeben. Für den Beweis müssen wir den \li-Move--Wert auseinandernehmen, um verwenden zu können, dass \li-picked p- auch wirklich nicht Null ist.

\begin{code}
play : (m n : ℕ) → n < m → Strategy → Strategy → List ℕ 
play 0 _ () _ _
play (suc m) 0 _ _ _ = []
play (suc m) (suc n) (s≤s n<m) p1 p2 with p1 (suc n)
... | pick k _ = suc n ∷ play m (suc n ∸ suc k) n-k<m p2 p1
  where n-k<m = start n ∸ k <⟨ s≤s (n∸m≤n k n) ⟩ n <⟨ n<m ⟩ m □
\end{code}

Die erste Zeile hat jetzt keine rechte Seite mehr, dafür steht da ein \li-()- als Pattern für den Beweis \li-n < 0-. Das ist das sogenannte absurde Pattern und kann verwendet werden wenn klar ist, dass es keinen Wert von diesem Typ geben kann. Damit haben wir statisch sichergestellt dass \li-m- nie Null wird.

\begin{comment}
\begin{code}
player1 : Strategy
player1 _ = pick 0 (s≤s (s≤s z≤n))
player2 : Strategy
player2 _ = pick 1 (s≤s (s≤s (s≤s z≤n)))
\end{code}
\end{comment}

Wenn wir jetzt \li-play- verwenden, müssen wir einen Beweis übergeben, dass die Parameter die Bedingungen erfüllen:
\begin{code}
winner : ℕ → Strategy → Strategy → Bool
winner n p1 p2 = evenList (play (suc n) n ≤-refl p1 p2)
\end{code}
