# 任意有限层的一步回灌保Good

同一算法对所有n：0送1，后继重复，ℕ极限逐点，旧种类保留，新种类
用真实低阶输出回灌，种子1。当前证明是一步折叠，不擅自等同于原M
跨多层direct fold；连接原OriginalPointwise仍需运行器模拟。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedFiniteRegFold where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedFiniteRegIf
open import OCF.Align.BoundedFiniteRegSub
open import OCF.Align.BoundedFiniteRegClosure

down : ∀ n → HB (F (suc n)) → HB (F n)
down n hz = one n
down n (hs a) = Ops.repeat (F n) (down n a)
down n (hl f) = hl (λ j → down n (f j))
down n (hΩ (inj₁ κ) g) = hΩ κ (λ c → down n (g c))
down n (hΩ (inj₂ _) g) = Ops.sum (F n) (λ j → down n (g (chain (λ c → down n (g c)) j)))

down-position : ∀ n {a b W} → RegWorld n W → Reg (suc n) b →
  a ⊲[ (W , one n) ] b → down n a ⊲[ W ] down n b
down-position n rw r hself = hself
down-position n rw r (hsuc p) = ⊲ᴮ-tr (down-position n rw r p) (hlim zero hself)
down-position n rw r (hlim j p) = hlim j (down-position n rw (r j) p)
down-position n rw (mo , r) (hLim {κ = inj₁ κ} b p) =
  hLim b (down-position n rw (r _ (reg-coordinate n κ rw b)) p)
down-position n rw (mo , r) (hLim {κ = inj₂ _} b p) =
  ⊲ᴮ-tr (down-position n rw (r _ (reg-sub n rw (reg-one n) b)) p)
    (⊲ᴮ-tr (down-position n rw (r (one n) (reg-one n)) (mo rw b hself b)) (hlim zero hself))

down-reg : ∀ n a → Reg (suc n) a → Reg n (down n a)
down-reg zero a r = tt
down-reg (suc n) hz r = reg-one (suc n)
down-reg (suc n) (hs a) r = reg-sum (suc n) _ (λ j → down-reg (suc n) a r)
down-reg (suc n) (hl f) r = λ j → down-reg (suc n) (f j) (r j)
down-reg (suc n) (hΩ (inj₁ κ) g) (mo , r) =
  seed-map (suc n) (λ W → W , one (suc n)) (λ W → W) κ g (λ c → down (suc n) (g c))
    (λ W rw c d rc rd p → down-position (suc n) rw (r d rd) p) mo ,
  (λ c rc → down-reg (suc n) (g c) (r c rc))
down-reg (suc n) (hΩ (inj₂ _) g) (mo , r) = reg-sum (suc n) _ outputs
  where
  feedback : HB (F (suc n)) → HB (F (suc n))
  feedback c = down (suc n) (g c)
  reg-chain : ∀ j → Reg (suc n) (chain feedback j)
  reg-chain zero = reg-one (suc n)
  reg-chain (suc j) = reg-add (suc n) _ _ (reg-chain j)
    (down-reg (suc n) (g _) (r _ (reg-chain j)))
  outputs : ∀ j → Reg (suc n) (feedback (chain feedback j))
  outputs j = down-reg (suc n) (g _) (r _ (reg-chain j))

down-legal : ∀ n a → Reg (suc n) a → Legal (suc n) a → Legal n (down n a)
down-legal n hz r l = legal-one n
down-legal n (hs a) r l = legal-sum n _ (λ j → down-legal n a r l)
down-legal n (hl f) r (st , l) = legal-lim n _
  (λ rw j → down-position n rw (r (suc j)) (st (rw , reg-one n) j))
  (λ j → down-legal n (f j) (r j) (l j))
down-legal n (hΩ (inj₁ κ) g) (sm , r) (mo , l) = legal-node n κ _
  (λ lw b b′ p → down-position n (world-reg n lw)
    (r _ (reg-coordinate n κ (world-reg n lw) b′)) (mo (lw , good-one n) b b′ p))
  (λ c lc → down-legal n (g c) (r c (coord-reg n κ c lc)) (l c lc))
down-legal n (hΩ (inj₂ _) g) (sm , r) (mo , l) = legal-sum n _ outputs
  where
  feedback : HB (F n) → HB (F n)
  feedback c = down n (g c)
  good-feedback : ∀ c → Good n c → Good n (feedback c)
  good-feedback c (rc , lc) = down-reg n (g c) (r c rc) , down-legal n (g c) (r c rc) (l c (rc , lc))
  good-chain : ∀ j → Good n (chain feedback j)
  good-chain zero = good-one n
  good-chain (suc j) = good-add n _ _ (good-chain j) (good-feedback _ (good-chain j))
  outputs : ∀ j → Legal n (feedback (chain feedback j))
  outputs j = proj₂ (good-feedback _ (good-chain j))

down-good : ∀ n a → Good (suc n) a → Good n (down n a)
down-good n a (r , l) = down-reg n a r , down-legal n a r l
```

down-position在RegWorld下，0层RegWorld为真，故最终位置结论仍对全部
P-world成立；最终Legal0是原LgB。没有给任意raw中间LgB保留的假定。
