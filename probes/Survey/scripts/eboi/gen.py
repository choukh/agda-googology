from eboi import *
from test2data import pool
def ag(t):
    if not t: return '[]'
    return '('+' ∷ '.join(agP(x) for x in t)+' ∷ [])'
def agP(x):
    if x==IP: return 'I'
    if x[0]=='L': return '(ψI %s)'%ag(x[1])
    return '(ψ %s %s)'%(ag(x[1]),ag(x[2]))
N=len(pool)
out=['{-# OPTIONS --cubical-compatible --guardedness --lossy-unification #-}','module SetzerTest where',
'open import OCF.Align.EBOI','open import Data.Nat using (ℕ)','open import Data.List using (List; []; _∷_; length)','open import Data.Bool using (Bool; true; false; _∧_; not)','open import Relation.Binary.PropositionalEquality using (_≡_; refl)',
'import Mahlo.Inacc.Syntax as S','import Mahlo.Inacc.Order as O','import Mahlo.Inacc.Closure as C',
'τL : T → List S.PTm','τP : PT → S.PTm','τT : T → S.Tm','τT t = S.fromList (τL t)',
'τL [] = []','τL (x ∷ xs) = τP x ∷ τL xs','τP (ψ [] []) = S.phi S.zer S.zer','τP (ψ (w ∷ ws) []) = S.Om (S.fromList (τL (w ∷ ws)))',
'τP (ψ u (y ∷ ys)) = S.psi (S.ΩR (S.fromList (τL u) S.▹ S.phi S.zer S.zer)) (S.fromList (τL (y ∷ ys)))','τP (ψI a) = S.psi S.IR (S.fromList (τL a))','τP I = S.I',
'eqB : Bool → Bool → Bool','eqB true b = b','eqB false b = not b',
'allB : ∀ {A : Set} → (A → Bool) → List A → Bool','allB p [] = true','allB p (x ∷ xs) = p x ∧ allB p xs',
'pool : List T','pool = '+' ∷\n  '.join(ag(t) for t in pool)+' ∷ []',
'_ : allB (λ t → eqB (isNF t) (C.isOT (τT t))) pool ≡ true','_ = refl',
'_ : allB (λ s → allB (λ t → eqB (s <? t) (O.lt (τT s) (τT t))) pool) pool ≡ true','_ = refl',
'']
k=0
for t in pool:
    c=cof(t)
    if c[0] in 'w1':
        for n in ([0,1,2] if c[0]=='w' else [0]):
            out+=['_ : fsn %s %d ≡ %s'%(ag(t),n,ag(fsn(t,n))),'_ = refl'];k+=1
open('../setzer/SetzerTest.agda','w').write('\n'.join(out)+'\n')
print('pool',N,'fsn checks',k,'NF',sum(isNF(t) for t in pool))
