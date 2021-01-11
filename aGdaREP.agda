module aGdaREP where

open import Data.Unit.Polymorphic using (⊤)
open import Data.Bool.Base using (Bool; true; false; not; if_then_else_)
open import Data.Char as Char using (Char; _≈_)
import Data.Char.Properties as Charₚ
open import Data.String.Base as String using (String; lines)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe′; when)
open import Data.Product using (_×_; _,_; uncurry)

open import System.Environment using (getArgs)

open import Function using (_$_; id; case_of_; _∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Text.Regex.Base Charₚ.≤-preorder using (updateExp)
open import Text.Regex.Char

open import Data.List.Relation.Binary.Infix.Heterogeneous using (Infix; MkView; toView)
open import aGdaREP.Options as Options using (Options; FilePath; usage); open Options.Options

select : Options → Regex → String → Maybe String
select opt e str = case search target regex of λ where
    (yes match) → when (not $ -v opt) (grab match)
    (no _)      → when (-v opt) str

   where

    regex : Regex
    regex = (if -i opt then updateExp ignoreCase else id) e

    exp : Exp
    exp = Regex.expression regex

    target : List Char
    target = String.toList str

    grab : ∀ {cs} → Match (Span regex _≡_) cs exp  → String
    grab (mkMatch inf _ prf) with toView (toInfix regex prf)
    ... | MkView pref _ suff = String.fromList
         $ pref ++ String.toList "\x1B[1m\x1B[31m"
        ++ inf  ++ String.toList "\x1B[0m"
        ++ suff

open import IO                    as IO
open import Codata.Musical.Colist as Colist

display : FilePath → String → String
display fp str = String.concat ("\x1B[35m" ∷ fp ∷ "\x1B[36m:\x1B[0m" ∷ str ∷ [])

grep : Options → Regex → List FilePath → IO ⊤
grep opt reg = List.mapM′ $ λ fp → do
  content ← readFiniteFile fp
  let ls = lines content
  List.mapM′ (maybe′ (putStrLn ∘ display fp) (return _))
    $ List.map (select opt reg) ls

main : _
main = IO.run $ do
  args ← getArgs
  let options = Options.parse args
  if -h options then putStrLn usage
    else if -V options then putStrLn "aGdaREP: version 0.2"
    else case regexp options of λ where
      nothing  → putStrLn usage
      (just e) → case parse e of λ where
        nothing      → putStrLn ("*** Error: invalid regexp")
        (just regex) → grep options regex (files options)
