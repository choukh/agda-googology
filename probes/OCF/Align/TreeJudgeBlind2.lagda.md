# 盲测二: $\psi_1(\Omega)$ 的紧读法, 预测 (写在比较之前, 不再改)

> **这个文件是预测, 写完就封存.** 结论写在 [TreeJudge](TreeJudge.lagda.md). 结果在 [TreeJudgeBlindResult](TreeJudgeBlindResult.lagda.md), [TreeJudgeAccept](TreeJudgeAccept.lagda.md). 不含记号. `p…` 是 `Bool`, 预测它算出 `true`.
>
> **为什么有第二次.** 第一次 ($A,B,C,D$) 的定义只新写了读法的实例, 折叠是现成的, 难度不高. 这一次的定义是 [GuardTight](GuardTight.lagda.md) 文件头说 "没有写, 判断要 `Str`/`Cont`" 的东西: $\psi_1(\Omega)$ 的紧读法 `Tc-F1` ([TreeJudgeRdF](TreeJudgeRdF.lagda.md)).
>
> **目标.** $E=\psi_0(\Omega_{\psi_1(\Omega)})$, $E^+=\psi_0(\Omega_{\psi_1(\Omega)+1})$. $E$ 有过种类测试 (`Tc-id`), $E^+$ 没有.
>
> **手算.** 同 [TreeJudgeBlind](TreeJudgeBlind.lagda.md) 的行律. $\psi_1(\Omega)$ 的层号是闭包, 第一支 $G(1)=a$, 分支 $\eta$ 是 $G(\eta)=\psi_1(\eta)$. 所以 $E$: 界 1, 头与第一支 $T(a)$, 分支 $\eta=1$ 是 $T(a)$, $\eta=2$ 是 $T(\psi_1(2))$.
> $E^+[0]=E$. $E^+[1]=\psi_0(\psi_W(\dot\Omega_W))$, $W=\psi_1(\Omega)$: 闭包保留在目标 $W$ 里, 被 $\psi_0$ 计值, 界 1, 头是 $\psi_0(\psi_W(\dot\Omega_a))$, $\dot\Omega_a$ 是极限所以头是极限. $E^+[2]$ 同样: 界 1.
>
> **界 (`Yt`, `Yi`): 这是这次的关键预测.** 闭包 $W$ 嵌进 $W+1$, 目标是 $0$, 路径穿过分支 $\tau$ 到 $\psi_1(\tau)$ 里的第 0 层 (路径 `pthG`). 紧读法: 位置一路落在前缀上, 落到第一支, 所以不读 $\tau$, 界 1, 对 $\tau=2,3,5$ (`pY1`..`pY3`). 恒等读法: 界 $\tau$ (`pY4`..`pY6`), 这是 `c-bra*` 在 $\psi_1(\Omega)$ 上的形式.
>
> **同头同界.** 紧读法不报, 恒等读法报 (深 11). `pB14` 那一次恒等读法在深 9 没报, 所以这里加了深度; 这是看了第一次的结果之后定的, 如实写.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudgeBlind2 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Prefix using (Z)
open import OCF.Align.GuardTightCum using (Ordᴵ; natᴵ; _⊑ᴵ_; _<ᴵ_; s⊑; z≅; zero; suc; lim)
open import OCF.Align.GuardTightLv
open Lv Dom₀
import OCF.Align.GuardTightUni as Uni
private module U = Uni Dom₀
open U using (F; Cf-F; rb₁)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree using (T₀; O; module Fold; module Emb; Ω̇; oŝ; owk; ocv; omk; ol; os; o0; oĉ; oΩ; ocl)
open import OCF.Align.TreeJudgeRdF using (Tc-F1; G; Tc-ψ)
open import OCF.Align.TreeJudgeObs
open import OCF.Align.TreeJudgeRead using (toN) renaming (rd to rdO)
open import OCF.Align.TreeJudgeBlind using (Ta; TC; isSh; is; same; hsame; noVio; sucCf)
```

## §1 树

```agda
W₁ : LG
W₁ = F (suc zero)

Cf-W : Cfˢ W₁
Cf-W = Cf-F (suc zero)

TE TE⁺ TE⁺id : Obs
TE = rdO (T₀ W₁ Cf-W Tc-F1)
TE⁺ = rdO (T₀ (suc W₁) (sucCf Cf-W) Tc-F1)
TE⁺id = rdO (T₀ (suc W₁) (sucCf Cf-W) (Tc-id (suc W₁)))
```

## §2 界: 目标的路径穿过分支 $\tau$

与 [GuardTightAccept](GuardTightAccept.lagda.md) 的 `Tgt` 同形, 这里不读记号. `pthG`: $G(\tau)$ 里到第 0 层的路径, 走前缀.

```agda
cO : ∀ {t ρ} → O t ρ → ℕ
cO (oŝ c _ _) = toN c
cO (owk _ x) = cO x
cO (ocv _ x) = cO x
cO (omk _ _ _ _ x) = cO x
cO (ol f) = 100
cO (os f) = 101
cO o0 = 102
cO (oĉ c _ _ _ _) = 103
cO (oΩ _ _ _) = 104
cO (ocl _ _ _ _ _) = 105

zero<nat : ∀ k → zero <ᴵ natᴵ (suc k)
zero<nat zero    = zero
zero<nat (suc k) = suc (zero<nat k)

one⊑nat : ∀ k → suc zero ⊑ᴵ natᴵ (suc k)
one⊑nat k = s⊑ z≅ (zero<nat k)

pthG : ∀ n → zero < G (natᴵ (suc n))
pthG zero    = lim 1 (fst zero)
pthG (suc n) = lim 1 (pthG n)

adm-pthG : ∀ n E → Adm E (pthG n)
adm-pthG zero E = tt
adm-pthG (suc n) E = adm-pthG n E

c₀ : LG
c₀ = suc W₁

module Tgt (n : ℕ) (tc₀ : Tc c₀) where
  τ : Ordᴵ
  τ = natᴵ (suc n)
  eτ : suc zero ⊑ᴵ τ
  eτ = one⊑nat n
  E : Ents
  E = ∅ (suc τ)
  q : zero < c₀
  q = suc (bra τ eτ (pthG n))
  aq : Adm (tab E) q
  aq = (suc τ , refl , suc zero) , adm-pthG n (tab E)
  open Fold c₀ (proj₁ Cf-W) (s≈ (proj₂ Cf-W)) tc₀
  nq = nfT c₀ tc₀ q
  Y : O (repT nq) tz
  Y = ψ E (tp (pathT nq) (tabT nq E aq)) (λ ()) (ι′ (Ω̇ W₁ Tc-F1))
    where
    ι′ : O W₁ tz → O c₀ tz
    ι′ z = owk (λ { (ml ()) ; (mr ()) }) (Emb.ι c₀ tc₀ W₁ (suc self) (inj₂ refl) z)

Yt Yi : ℕ → ℕ
Yt n = cO (Tgt.Y n Tc-F1)
Yi n = cO (Tgt.Y n (Tc-id c₀))
```

## §3 预测

```agda
hdIs : List St → Obs → Sh → Bool
hdIs p x s = isSh (shape (hdOf (go p x))) s

sameAtHd : List St → List St → Obs → Bool
sameAtHd p r x = sameM 7 2 (go p x) (hdOf (go r x))

sameAt : List St → List St → Obs → Bool
sameAt p r x = sameM 7 2 (go p x) (go r x)

pE1 = is [] TE (shc 1)
pE2 = hsame [] TE Ta
pE3 = same (fs ∷ []) TE Ta
pE4 = same (br 0 ∷ []) TE Ta
pE5 = same (br 1 ∷ []) TE TC
pE6 = noVio (run 9 9 2 TE)

pF1 = is [] TE⁺ shl
pF2 = same (lm 0 ∷ []) TE⁺ TE
pF3 = is (lm 1 ∷ []) TE⁺ (shc 1)
pF4 = hdIs (lm 1 ∷ []) TE⁺ shl
pF5 = sameAtHd (lm 1 ∷ fs ∷ []) (lm 1 ∷ []) TE⁺
pF6 = is (lm 2 ∷ []) TE⁺ (shc 1)
pF7 = sameAt (lm 1 ∷ br 0 ∷ []) (lm 1 ∷ fs ∷ []) TE⁺
pF8 = noVio (run 9 9 2 TE⁺)

-- 界
_≟_ : ℕ → ℕ → Bool
_≟_ = _==_

pY1 = Yt 1 ≟ 1
pY2 = Yt 2 ≟ 1
pY3 = Yt 4 ≟ 1
pY4 = Yi 1 ≟ 2
pY5 = Yi 2 ≟ 3
pY6 = Yi 4 ≟ 5

-- 同头同界, 深 11: 紧的不报, 恒等的报
pH1 = noVio (run 11 8 2 TE⁺)
pH2 = not (noVio (run 11 8 2 TE⁺id))
```
