# 结构关系, 第十六轮 (五): 两种混合种类的输出对在 `RelX⁺` 里; `¬laterV` 的那一对不在

> 不读记号. 入口 [StrRel16](StrRel16.lagda.md). 接口 [StrRel16If](StrRel16If.lagda.md). 实例 $\Lambda_2=2$, 节点 `xL` (坐标层 $0$), `xR` (坐标层 $1$), 分支常数 `n1`, 世界 $0$, 路径 `self`, 动作 `Act`, 上下文 `n0`.
>
> 1. **(定理) `krAt`: 左留右升的输出对在 `RelX⁺` 里, 无条件.** 状态 $Y_1$, 目标对 (第 $1$ 层, 第 $1$ 层) (`StrRel15Bar.¬oblKR` 的那一对): 左 `xL` 留成节点 (坐标层 $0$), 右 `xR` 升成链. 推导: 链的第 $0$ 项是 $Y_1$ 在第 $1$ 层的读数 $0⨾\omega\cdot(\Omega_1⨾0)$ 的运行, 其中 $\Omega_1=1⨾\mathrm{ni}\ldots$ 的节点在第 $1$ 层目标上保留; 左节点 $\le$ 这个节点 (`ni⁺`, 坐标层 $0\sqsubseteq_\infty 0$), 它是链的分量 (`In`: 第 $0$ 项, 右, 第 $0$ 项, 左, 右), 所以由 `in⁺` 得结论. 分支的比较用 `StrRel16Sem.semX00⁺` (输入在坐标层 $0$, 第 $0$ 层对第 $0$ 层, 无条件) 与 `lawcv⁺`.
> 2. **(定理) `rkAt`, `rkAtLR`: 左升右留的两对输出在 `RelX⁺` 里** (`rk⁺` 的实例, 前提全部填上). `rkAt`: `xL` 对 `xL`, 目标对 (第 $0$ 层, 第 $1$ 层) (`StrRel15Bar.¬semXLL` 的那一对); `rkAtLR`: `xL` 对 `xR`, 目标对 (第 $0$ 层, 第 $2$ 层).
> 3. **(否定) `¬laterPair`: `StrRel13Later.¬laterV` 的那一对 (状态 $Y_0$, 左留右升) 不在 `RelX⁺` 里.** 右边的链每一项都是 `n0` (`StrRel13Later.stz`); `RelX⁺` 里能以 "左 `ni`, 右 `nl`" 为结论的只有 `in⁺` (要节点 $\le$ 链的某一项的某个分量, 而 `n0` 的分量只有 `n0`) 与 `rk⁺` (它的左边是 `nl`, 与 `ni` 不合); 节点 $\le$ `n0` 也推不出 (`¬niN0`). 所以 `RelX⁺` 不撞 `¬laterV`: 那里的值的反例 (左边非零, 右边为零) 不是 `RelX⁺` 里的一对.
>
> **只否定什么.** 第 3 条只说那一对 (空状态下的左留右升输出) 不 `RelX⁺` 相关, 对任何把 "节点 ≤ 链" 写成 `in⁺` 的关系; 不说 `RelX⁺` 可靠.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel16Kr where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (azero; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (H; hz; hs; hself; hsuc; ss; StH; Vs; D; n0; n1; nl; ni; accL; ⊲ᴴ↑)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel12Al using (cp-top; cp-tr)
import OCF.Align.StrRel11Rk as Rk
import OCF.Align.StrRel14If as If
open import OCF.Align.StrRel13Val using (Λ₂; r₀; r₁; xL; xR; cp00)
open import OCF.Align.StrRel13Kr using (OutL₁; OutR₁)
open import OCF.Align.StrRel13Later using (stz)
open import OCF.Align.StrRel15Fin using (module FinΛ; T₁)
open import OCF.Align.StrRel16If Λ₂ tt
open import OCF.Align.StrRel16Sem Λ₂ tt using (lawcv⁺; jPfx⁺; semX00⁺)
open import OCF.Align.StrRel16Fin using (module FinΛ⁺)
open import OCF.Align.StrRel16Lem using (Lp; here; left)

open Rk Λ₂ tt using (s∞; u∞)
open If Λ₂ tt using (n0ˣ; n1ˣ)
open FinΛ Λ₂ tt tt using (hawAct²; hY₁)
open FinΛ⁺ Λ₂ tt tt using (ΩRX²⁺; stepOA²⁺; Y₁; hY₁⁺)
open P using (Tg; tg; τ₀; St; yc; Run; Act)
```

## 1 左留右升: `xL` 对 `xR`, 目标对 $(1,1)$

```agda
module X = NodeObl²⁺ {lV = tt} {lV′ = tt} r₀ r₁ (λ _ _ _ → n1) (λ _ _ _ → n1) tt tt
                     (accL Λ₂) (accL hz) (accL Λ₂) (accL (hs hz)) C.self C.self hself hself Act Act n0 n0 (Y₁ tt) (Y₁ tt)

-- xR 的链第 0 项里, Ω₁ 的节点处的状态: Y₁ 向右延长两次
S° : St azero
S° = (Y₁ {azero} tt P.⊕⟨ tt ⟩ P.zeroD) P.⊕⟨ tt ⟩ P.Step (Y₁ {azero} tt P.⊕⟨ tt ⟩ P.zeroD)

hS° : J²⁺ {azero} {azero} tt tt (Y₁ tt) S°
hS° = jPfx⁺ (hY₁⁺ {azero} {azero} tt tt) ((λ T → left (left here)) , left (left here))

krAt : X.Out²⁺ T₁ T₁ (P.keep (ss hself)) P.rise
krAt =
  in⁺
    (ni⁺ s∞
      (λ p p′ lc lc′ cp y y′ hb →
         nl⁺ (λ _ → ⨾⁺ (ΩRX²⁺ tt tt s∞)
                        (⨾⁺ (proj₁ (proj₁ (lawcv⁺ (proj₁ (cp-tr (proj₁ cp00) cp)) (Y₁ tt) S°
                                      hS°))
                               (tg C.self (⊲ᴴ↑ p (hsuc hself)) lc) (tg C.self (⊲ᴴ↑ p′ (hsuc hself)) lc′) (cp-top (cp-tr (proj₁ cp00) cp) , s∞))
                             (semX00⁺ hb lc lc′ _ _ _ _ C.self C.self (cp-top (cp-tr (proj₁ cp00) cp)) _ _
                                (λ p₁ p₁′ l l′ cp₁ w w′ hw Y Y′ hY → stepOA²⁺ hY) n0 n0 n0⁺ _ _
                                (lawcv⁺ (proj₁ (cp-tr (proj₁ cp00) cp)) (Y₁ tt) S°
                                   hS°)
                                _ _ (cp-top (cp-tr (proj₁ cp00) cp) , s∞))))))
    (inE 0 (inR (inE 0 (inL (inR here)))))
```

## 2 左升右留: `rk⁺` 的两个实例

```agda
T₀ : Tg azero hz azero
T₀ = τ₀ tt

T₂ : Tg azero Λ₂ azero
T₂ = tg C.self hself tt

module S = NodeObl²⁺ {lV = tt} {lV′ = tt} r₀ r₀ (λ _ _ _ → n1) (λ _ _ _ → n1) tt tt
                     (accL Λ₂) (accL hz) (accL Λ₂) (accL hz) C.self C.self hself hself Act Act n0 n0 (Y₁ tt) (Y₁ tt)

rkAt : S.Out²⁺ T₀ T₁ P.rise (P.keep (ss hself))
rkAt = rk⁺ r₀ r₀ tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL hz) C.self C.self hself hself Act Act n0 n0 (Y₁ tt) (Y₁ tt) T₀ T₁ (ss hself)
         (cp00 , (s∞ , ((λ p p′ lc lc′ cp y y′ b → n1ˣ) , (hawAct² Λ₂ Λ₂ , (n0ˣ , hY₁ tt tt)))))
         (cp00 , u∞ s∞) refl refl

rkAtLR : X.Out²⁺ T₀ T₂ P.rise (P.keep (ss hself))
rkAtLR = rk⁺ r₀ r₁ tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL (hs hz)) C.self C.self hself hself Act Act n0 n0 (Y₁ tt) (Y₁ tt) T₀ T₂ (ss hself)
           (cp00 , (u∞ s∞ , ((λ p p′ lc lc′ cp y y′ b → n1ˣ) , (hawAct² Λ₂ Λ₂ , (n0ˣ , hY₁ tt tt)))))
           (cp00 , u∞ (u∞ s∞)) refl refl
```

## 3 `¬laterV` 的那一对不在 `RelX⁺` 里

```agda
in0 : ∀ {L V} {y : D L V} → In y n0 → y ≡ n0
in0 here = refl

¬niN0 : ∀ {L L′ V V′ k} {lV : Lg V} {lV′ : Lg V′} {r : StH V k L} {u : ∀ {W′} → V C.⊲ W′ → Lg W′ → Vs L r W′ → D L W′} →
        ¬ RelX⁺ L L′ lV lV′ (ni r u) n0
¬niN0 (in⁺ h here) = ¬niN0 h

¬niNl : ∀ {L L′ V V′ k} {lV : Lg V} {lV′ : Lg V′} {r : StH V k L} {u : ∀ {W′} → V C.⊲ W′ → Lg W′ → Vs L r W′ → D L W′}
          {e : ℕ → D L′ V′} → (∀ n → e n ≡ n0) → ¬ RelX⁺ L L′ lV lV′ (ni r u) (nl e)
¬niNl ez (in⁺ h here) = ¬niNl ez h
¬niNl {L = L} {L′} {lV = lV} {lV′} {r = r} {u} ez (in⁺ h (inE n p)) =
  ¬niN0 (subst (RelX⁺ L L′ lV lV′ (ni r u)) (in0 (subst (In _) (ez n) p)) h)

¬laterPair : ¬ RelX⁺ (hs hz) (hs hz) tt tt OutL₁ OutR₁
¬laterPair = ¬niNl (λ n → stz _ _ tt _ P.Y₀ refl T₁ n)
```
