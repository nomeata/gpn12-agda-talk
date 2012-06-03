\begin{comment}
\begin{code}
module Pebbels2 where

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

In herkömmlichen Programmiersprachen würde man jetzt vermutlich in \li-play- eine Abfrage einfügen, ob der Spieler versuchte, keine Murmel zu nehmen, und dann z.B. eine Exception schmeißen. Es geht aber auch eleganter: Wir wollen dass der Compiler ungültige Spielzüge schon beim Kompilieren ausschließt. 

Dazu nutzen wir aus dass \li-ℕ- nicht alle ganzen Zahlen sind, sondern nur die natürlichen (beginnend bei 0). Wir speichern im \li-Move--Datentyp also nicht mehr die Anzahl der genommen Murmeln, sondern eine weniger, und rechnen nachher wieder eine drauf. Damit wir das nicht vergessen packen wir die gewählte Zahl in einen eigenen Datentypen, mit Konstruktor \li-pick-, und schreiben eine Funktion \li-picked- die die Zahl wieder herausholt:
\begin{code}
data Move : Set where
  pick : ℕ → Move

picked : Move → ℕ
picked (pick n) = suc n

Strategy = ℕ → Move 
\end{code}

Die \li-play-Funktion und unsere beiden ehrlichen Spieler werden jetzt leicht angepasst. Den Spieler \li-player0- können wir nun gar nicht mehr schreiben!
\begin{code}
play : ℕ → Strategy → Strategy → List ℕ 
play 0 _ _ = []
play n p1 p2 with p1 n
... | p = n ∷ play (n ∸ picked p) p2 p1

player1 : Strategy
player1 _ = pick 0
player2 : Strategy
player2 _ = pick 1
\end{code}

\begin{comment}
\begin{code}
evenList : {A : Set} → List A → Bool
evenList [] = true
evenList (_ ∷ xs) = not (evenList xs)
winner : ℕ → Strategy → Strategy → Bool
winner n p1 p2 = evenList (play n p1 p2)
\end{code}
\end{comment}

\section{Mehr Bescheißerei!}

Leider ist das immer noch nicht so ganz wasserdicht, folgender klugscheißender Spieler kann immernoch jedes Spiel gewinnen:
\begin{code}
playerN : Strategy
playerN 0 = pick 0 -- Der Fall kommt eignetlich nicht vor.
playerN 1 = pick 0 -- Naja, so verlieren wir natürlich noch.
playerN (suc (suc n)) = pick n -- Wir nehmen alle bis auf eine.
\end{code}
