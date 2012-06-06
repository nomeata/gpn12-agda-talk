\section{Der erste Versuch}

Unsere Aufgabe ist es nun einen Simulator für dieses einfache Spiel zu schreiben. Dazu legen wir eine neue Agda-Datei an und importieren erstmal ganz viele Module, die wir jetzt oder später brauchen werden:

\begin{code}
module Pebbels1 where

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

Das letzte Modul ist ein Hilfsmodul für diesen Vortrag mit ein paar arithmetischen Lemmas, die wir hier nicht widergeben wollen.

Als nächstes definieren wir ein paar Typen für unsere Aufgabe. Ein Spielzug ist eine natürliche Zahl, diese Paken wir in einen eigenen Datentypen um nicht zum beispiel Spielzüge und Anzahl der Murmlen auf dem Tisch durcheinander zu bringen. Eine Spielstrategie ist eine Funktion, die jeder natürlichen Zahl einen Spielzug zuweist. Für diese UTF8-Sonderzeichen gibt es im Emacs im Agda-Modus spezielle Eingabefolgen, etwa \verb-\bn- für $\mathbb N$ und \verb-\to- für~$\to$.
\begin{code}
data Move : Set where
  pick : ℕ → Move
picked : Move → ℕ
picked (pick k) = k
Strategy = ℕ → Move 
\end{code}

Nun definiern wir die Simulation, erstmal wie in einer stink-normalen funktionalen Programmiersprache wie Haskell. Neu ist hierbei höchstens das \lstinline-with--Konstrukt, es entspricht einem \lstinline-case ... of-, nur dass in der Fallunterscheidung alle Parameter der Funktion erneut wiederholt werden können -- das wird später noch wichtig. Da wir die Parameter nicht ändern Der Unterstricht steht für eine Variable, die uns nicht 
\begin{code}
play : ℕ → Strategy → Strategy → List ℕ 
play 0 _ _ = []
play n p1 p2 with p1 n
... | p = n ∷ play (n ∸ picked p) p2 p1
\end{code}

Nun können wir zwei Spieler mit recht einfachen Strategien definieren; der erste nimmt immer zwei Murmeln, der zweite immer zwei:
\begin{code}
player1 : Strategy
player1 _ = pick 1
player2 : Strategy
player2 _ = pick 2
\end{code}

Schon können wir mit dem Code herumspielen. Erst wird er mittels \keystroke{Strg}\keystroke C\keystroke L geprüft und kompiliert. Mittels \keystroke{Strg}\keystroke C\keystroke N könen wir einen Ausdruck auswerten, etwa \lstinline-play 5 player1 player2-, das wertet zur Liste \lstinline-5 ∷ 4 ∷ 2 ∷ 1 ∷ []- aus (das ist \lstinline-[5,4,3,2,1]- in Haskell-Syntax).

Wir sehen, dass hier Spieler eins gewinnt, aber immer von Hand zu zählen ist uns zu mühsam, also definieren wir eine Funktion die prüft, ob eine Liste eine gerade Anzahl von Einträgen hat. Diese ist polymorph, also funktioniert mit beliebigen Listen-Elementen \lstinline-A-, aber der Parameter ist implizit (da in geschweiften Klammern) und muss beim Aufruf von \lstinline-evenList- nicht angegeben werden.
\begin{code}
evenList : {A : Set} → List A → Bool
evenList [] = true
evenList (_ ∷ xs) = not (evenList xs)
\end{code}

Zuletzt können wir die Funktion definieren, die sagt, ob der erste Spieler Gewinnt.
\begin{code}
winner : ℕ → Strategy → Strategy → Bool
winner n p1 p2 = evenList (play n p1 p2)
\end{code}
Damit wertet \lstinline-play 5 player1 player2- zu \lstinline-true- aus.

\section{Bescheißerei!}

Leider lässt sich dieser Code ganz schön an der Nase herumführen. Nehmen wir folgenden Spieler:
\begin{code}
player0 : Strategy
player0 _ = pick 0
\end{code}

Offensichtlich wird dieser Spieler nie verlieren, wie wir mit \keystroke{Strg}\keystroke C\keystroke N  stichprobenhaft nachprüfen können. Oder, vielleicht weniger offensichtlich, folgenden Spieler:

\begin{code}
playerN : Strategy
playerN n = pick (n ∸ 1)
\end{code}
Dieser lässt seinem Gegenüber immer genau eine Murmel übrig und kann damit auch nicht verlieren.

