\begin{comment}
\begin{code}
module Pebbels3 where

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

Wir müssen nun also sichergehen dass der Spieler höchstes 6 Murmeln nimm. Hier könnnen wir jetzt nicht mehr einfach nur einen vorhandenen Datentypen (miss-)brauchen. Eine möglichkeit wäre es, einen Aufzählungstypen mit 6 Elemente nzu definieren, aber das wäre hässlich, weil wir damit nicht mehr schön rechnen können, außerdem möchten wir den Code später vielleicht verallgemeinern und die Anzahl der Murmeln, die man nehmen darf, konfigurierbar machen.

Statt dessen betreten wir jetzt die Welt der abhängigen Typen. Das heißt dass in den Typen auch Werte auftauchen können. Insbesondere gibt es Typen für (fast) beliebige Aussagen über Werte, etwa „der Vektor \li-l- hat \li-n- Elemente“ oder, hier relevanter, „die Zahl \li-n- ist kleiner als die Zahl \li-m-“. Werte von diesem Typ sind dann Beweise, dass die Aussage stimmt. Wenn eine Funktion jetzt neben einem Wert auch einen solchen Beweis erwartet, dann kann ich sie nur aufrufen, wenn ich auch einen Beweis angebe. Die Funkion selbst wird vermutlich den Beweis nicht anschauen, aber kann sich darauf verlassen, dass die Aussage stimmt – sonst hätte ich keinen Beweis konstruieren können und die Funktion auch nicht aufrufen können.

Wir möchten sichergehen dass ein Wert vom Typ \li-Move- immer auch ein gültiger Zug ist. Dazu erwarten wir dass ein Move nicht nur aus einer natürlichen Zahl besteht, sondern auch aus einem Beweis dass die Zahl kleiner 7 ist:
\begin{code}
data Move : Set where
  pick : (n : ℕ) → suc n < 7 → Move

picked : Move → ℕ
picked (pick n _) = suc n
\end{code}

Beachte dass wir beim ersten Parameter nicht nur den Typ (\li-ℕ-) angeben, sondern ihm auch einen Namen geben, den wir im \emph{Typ} des zweiten Parameters wieder verwenden können.

\begin{comment}
\begin{code}
Strategy = ℕ → Move 
play : ℕ → Strategy → Strategy → List ℕ 
play 0 _ _ = []
play n p1 p2 with p1 n
... | p = n ∷ play (n ∸ picked p) p2 p1
\end{code}
\end{comment}

Da wir nur per \li-picked- auf den Move zugriefen, muss die \li-play--Funktion nicht geändert werden. Allerdings müssen die Spieler jetzt Beweise mit liefern. Agda kann uns helfen, diese zu finden, wir geben also erstmal nur ein Loch an:
\begin{lstlisting}
player1 : Strategy
player1 _ = pick 0 ?
player2 : Strategy
player2 _ = pick 1 ?
\end{lstlisting}

Nach dem Laden (\keystroke{Strg}\keystroke C\keystroke L) werden daraus Löcher, die man inspizieren kann, so kann man sich mit \keystroke{Strg}\keystroke C\keystroke , das aktuelle Ziel anzeigen, also den Typ, der an diesem Loch erwartet wird. Dort steht im erste Loch \li-2≤7-. Warum nicht \li-1<7-, wie wir es im Code angegeben haben? Weil \li-a<b- nur eine Abkürzung für \li-suc a ≤ b- ist, und Agda das Ziel soweit auswertet wie möglich.

In einfachen Fällen kann Agda sogar selbst herausfinden, welcher Code hier reinmuss, dazu probieren wir \keystroke{Strg}\keystroke C\keystroke A  (A für „auto“) und erhalten:
\begin{code}
player1 : Strategy
player1 _ = pick 0 (s≤s (s≤s z≤n))
player2 : Strategy
player2 _ = pick 1 (s≤s (s≤s (s≤s z≤n)))
\end{code}

Was heißt das? Anscheinend gibt es Funkionen namens \li-z≤n- und \li-s≤s-, mit denen man sich Kleiner-Gleich-Beweise zusammenbasteln kann. 
%Mit \agdastroke D kann man sich Typen von Werten anschauen.
Mit der mittleren Maustaste kann man direkt zur Definition einer Funktion springen. Dort sehen wir den folgenden Code:
\begin{lstlisting}
data _≤_ : Rel ℕ Level.zero where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n
\end{lstlisting}

In Worten: \li-z≤n- ist ein Beweis dass Null kleiner-gleich jeder Zahl ist, und dass ich einen Vergleich zweier Zahlen auf ihren Nachfolger übertragen kann. Also hat \li-s≤s (s≤s z≤n)- den Typ \li-suc (suc zero) ≤ suc (suc m)- für jede natürliche Zahl \li-m-. In unserem Fall heißt das, wie gewünscht \li-2≤7-.

\begin{comment}
\begin{code}
evenList : {A : Set} → List A → Bool
evenList [] = true
evenList (_ ∷ xs) = not (evenList xs)
winner : ℕ → Strategy → Strategy → Bool
winner n p1 p2 = evenList (play n p1 p2)
\end{code}
\end{comment}

So, was haben wir jetzt davon? Wir können nun auch \li-playerN- nicht mehr schreiben, denn es wird uns nicht gelingen \li-n<7- für beliebige \li-n- zu beweisen. Damit haben wir jetzt ungültige Spieler vollständig ausgeschlossen!

\section{Termination}

Oder haben wir wirklich? Es gibt ja noch diese verräterischen rot unterlegen Funktionsnamen, etwa \li-play-. Was es damit auf sich hat zeigt folgender Code:

\begin{code}
n≤7 : {n : ℕ} → n ≤ 7
n≤7 = n≤7

playerN : Strategy
playerN 0 = pick 0 (s≤s (s≤s z≤n))
playerN 1 = pick 0 (s≤s (s≤s z≤n))
playerN (suc (suc n)) = pick n n≤7
\end{code}

Tatsächlich akzeptiert der Typchecker den Code und ich kann \li-playerN- gegen die anderen Spieler antreten (und gewinnen) lassen! Das geht natürlich nicht mit rechten Dingen zu. Was wir gemacht haben ist, eine Funktion zu schreiben, die nicht terminiert; in der Definition von \li-n≤7- kommt ja wieder \li-n≤7- vor! Und wenn das erlaubt wäre, könnte man beliebige Aussagen beweisen; siehe oben.

Daher erwartet Agda dass aller Code terminierend ist. Wenn agda nicht überzeugt ist,dass das der Fall ist, dann läuft der Code zwar, aber wird eben rot hinterlegt. 

Und warum ist jetzt \li-play- rot hinterlegt – es terminiert doch in jedem Fall (schließlich ist \li-pick p- stets größer als 0). Leider sieht das agda nicht selbst und wir müssen nachhelfen.
