module aGdaREP where

open import Level
open import Codata.Musical.Notation
open import Data.Unit.Polymorphic using (⊤)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Char as Char using (Char; _≈_)
open import Data.String.Base as String using (String; unlines)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe′)
open import Data.Product using (_×_; _,_; uncurry)

open import System.Environment using (getArgs)

open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import lib.Nullary

open import Text.Regex.Char

open import Data.List.Relation.Binary.Infix.Heterogeneous using (Infix; MkView; toView)
open import aGdaREP.Options as Options using (Options; FilePath; usage); open Options.Options

select : Options → Regex → String → Maybe String
select opt e str = dec (search target regex) ifYes ifNo
  where
    regex : Regex
    regex = (if -i opt then updateExp ignoreCase else id) e

    exp : Exp
    exp = Regex.expression regex

    target : List Char
    target = String.toList str

    grab : ∀ {cs} → Match (Span regex _≡_) cs exp  → String
    grab (MkMatch inf _ prf) with toView (toInfix regex prf)
    ... | MkView pref _ suff = String.fromList
         $ pref ++ String.toList "\x1B[1m\x1B[31m"
        ++ inf  ++ String.toList "\x1B[0m"
        ++ suff

    ifYes = if -v opt then const nothing    else (just ∘′ grab)
    ifNo  = if -v opt then const (just str) else const nothing


open import IO                    as IO
open import Codata.Musical.Colist as Colist

breakOn : {A : Set} (P? : A → Bool) (xs : List A) → List (List A)
breakOn {A} P? = uncurry _∷_ ∘ List.foldr step ([] , [])
  where
    step : A → (List A × List (List A)) → (List A × List (List A))
    step a (xs , xss) = if (P? a) then [] , xs ∷ xss else a ∷ xs , xss

lines : String → List String
lines = List.map String.fromList ∘ breakOn isNewLine ∘ String.toList
  where
    isNewLine : Char → Bool
    isNewLine y = dec (y Char.≟ '\n') (const true) (const false)

display : FilePath → String → String
display fp str = String.concat ("\x1B[35m" ∷ fp ∷ "\x1B[36m:\x1B[0m" ∷ str ∷ [])

grep : Options → Regex → List FilePath → IO ⊤
grep opt reg []        = return _
grep opt reg (fp ∷ xs) =
  ♯ IO.readFiniteFile fp >>= λ content →
  ♯ (♯ (IO.mapM′ (maybe′ (putStrLn ∘ display fp) (return _))
       $ Colist.fromList
       $ List.map (select opt reg)
       $ lines content) >>
       ♯ (grep opt reg xs))

main : _
main =
  IO.run $
  ♯ getArgs >>= λ args →
    ♯ let options = Options.parse args in
      if -h options then putStrLn usage
      else if -V options then putStrLn "aGdaREP: version 0.2"
      else case regexp options of λ where
             nothing  → putStrLn usage
             (just e) → case parse e of λ where
                nothing      → putStrLn ("*** Error: invalid regexp")
                (just regex) → grep options regex (files options)
