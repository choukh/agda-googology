# 朝低层保持的五参数接口

> 判决: 接口与编译定理, 无前提, 不读记号 (只导入标准库与 `YiAbs*`, `YiFIIface`, `YiBLIface`, `YiQDIface`). 一条保持陈述 `Hold Φ ap D` 由五个参数定: 目标 (像的层), 路径 (像 Φ, 折叠里是 `ψ ℓ b j w β`), 上下文 (参照一侧的作用 ap, 头 ψ_ν 与前缀都在里面), 量化域 D, 不变式 (作前提, `Low I D` 的 I 或系统的 `Bdˢ`).
> 换算: `LowKeep`, `SelfKeep`, `UpKeep` 与新接口互推 (`lowKeep→`/`→lowKeep`, `selfKeep→`/`→selfKeep`, `upKeep→`/`→upKeep`); 状态形式 `KeepSys` 经 `sys→LowAt` 落到一点, 三份旧的 `sys→low` (FI, BL, QD) 是它的取值. 域与不变式上反变 (`hold-dom`, `low-mono`).
> 不给出什么: 不证任何一点上的保持; 具体折叠上的换算在 [YiMIConv](YiMIConv.lagda.md), 读记号的在 [YiMIRead](YiMIRead.lagda.md), 分级实例与生成原理在 [YiMIGraded](YiMIGraded.lagda.md), 自身折叠在 [YiMISelf](YiMISelf.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMIIface where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiBLIface
open import OCF.Lean.YiQDIface
```

## 接口

`Hold Φ ap D`: 第 ℓ 层的域 D 里的树 x, 参照 a 不高于 x 时, 像 Φ x 在第 j 层不低于 ap a. `LowAt` 是折叠的像与 `Graded` 的上下文; `Low I D` 对不变式 I 选出的一切点 (源层, 目标, 底, 路径, 底值, 上下文) 成立.

```agda
module MI {𝔹 : Block} {𝔽 : Fold 𝔹} {ℜ : Rows 𝔹 𝔽} {𝕋 : Ref} {𝕍 : Val}
          (𝔾 : Graded 𝔹 𝔽 ℜ 𝕋 𝕍) (𝔻 : Doms 𝔹 𝔽) where
  open Laws 𝔾 𝔻
  open FI 𝔾 𝔻 using (Sys; WfL; module Sys)

  Hold : ∀ {ℓ j} → (Tr ℓ → Tr j) → (T → T) → (Tr ℓ → Set) → Set
  Hold {ℓ} {j} Φ ap D = ∀ {a x} → D x → R ℓ a x → R j (ap a) (Φ x)

  LowAt : ∀ {ℓ j} → Bs ℓ → j ⊑ ℓ → Bt j → Cx ℓ j → (Tr ℓ → Set) → Set
  LowAt {ℓ} {j} b w β K D = Hold (ψ ℓ b j w β) (app K) D

  record Pt : Set where
    constructor pt
    field
      {src tgt} : Lv
      bs  : Bs src
      pth : tgt ⊑ src
      bv  : Bt tgt
      cx  : Cx src tgt
  open Pt public

  Low : (Pt → Set) → ((π : Pt) → Tr (src π) → Set) → Set
  Low I D = ∀ π → I π → LowAt (bs π) (pth π) (bv π) (cx π) (D π)

  ⊤ᴰ : ∀ {ℓ} → Tr ℓ → Set
  ⊤ᴰ _ = ⊤
```

域与不变式上反变.

```agda
  hold-dom : ∀ {ℓ j} {Φ : Tr ℓ → Tr j} {ap D D′} → (∀ {x} → D′ x → D x) → Hold Φ ap D → Hold Φ ap D′
  hold-dom sub P d r = P (sub d) r

  low-mono : ∀ {I I′ D D′} → (∀ π → I′ π → I π) → (∀ π {x} → D′ π x → D π x) → Low I D → Low I′ D′
  low-mono si sd L π i d r = L π (si π i) (sd π d) r

  hold-⊤ : ∀ {ℓ j} {Φ : Tr ℓ → Tr j} {ap D} → Hold Φ ap ⊤ᴰ → Hold Φ ap D
  hold-⊤ = hold-dom (λ _ → tt)
```

## 抽象接口的三条保持

`LowKeep`: I 是 `Gb × Wl × Bd`, D 是 `Gx`. `SelfKeep`: 目标即源层, 路径 `self`, 上下文 `cl ℓ (P ⊕ ·)`, 域全体. `UpKeep`: 像是上折 `upf d β`, 上下文 `cl ℓ (t ⊕ ·)`.

```agda
  Iᴷ : Pt → Set
  Iᴷ π = Gb (src π) (bs π) × Wl (pth π) × Bd (bs π) (pth π) (bv π) (cx π)

  Dᴷ : (π : Pt) → Tr (src π) → Set
  Dᴷ π = Gx (src π)

  lowKeep→ : LowKeep → Low Iᴷ Dᴷ
  lowKeep→ lk (pt b w β K) (gb , wl , bd) = lk b w β K gb wl bd

  →lowKeep : Low Iᴷ Dᴷ → LowKeep
  →lowKeep L b w β K gb wl bd = L (pt b w β K) (gb , wl , bd)

  SelfP : Set
  SelfP = ∀ {ℓ} (b : Bs ℓ) (β : Bt ℓ) → Gb ℓ b → ∀ {P} → R ℓ (cl ℓ P) (bt β)
        → Hold (ψ ℓ b ℓ self β) (λ a → cl ℓ (P ⊕ a)) ⊤ᴰ

  selfKeep→ : SelfKeep → SelfP
  selfKeep→ sk b β gb rb _ r = sk b β gb rb r

  →selfKeep : SelfP → SelfKeep
  →selfKeep sp b β gb rb r = sp b β gb rb tt r

  UpP : Set
  UpP = ∀ {ℓ j} (d : Dn ℓ j) (β : Bt ℓ) {t} → R ℓ (cl ℓ t) (bt β) → Hold (upf d β) (λ s → cl ℓ (t ⊕ s)) ⊤ᴰ

  upKeep→ : UpKeep → UpP
  upKeep→ uk d β rb _ r = uk d β rb r

  →upKeep : UpP → UpKeep
  →upKeep up d β rb r = up d β rb tt r
```

## 状态形式

`FI.Sys j`: 目标 j 固定, 路径与底在状态里 (像 Φ s), 上下文 (Cxt, ap), 不变式 `Bdˢ`; 域 D 随状态. `sys→LowAt`: 状态的像对上折叠、上下文对上 `app` 时落到一点.

```agda
  module _ {j : Lv} (𝒮 : Sys j) where
    open Sys 𝒮

    KeepSys : (∀ {a} → St a → Tr a → Set) → Set
    KeepSys D = ∀ {a} (s : St a) K → Bdˢ s K → Hold (Φ s) (ap K) (D s)

    sys→LowAt : {D : ∀ {a} → St a → Tr a → Set} → KeepSys D → ∀ {ℓ} (s : St ℓ) (K : Cxt) → Bdˢ s K
      → (b : Bs ℓ) (w : j ⊑ ℓ) (β : Bt j) (Kc : Cx ℓ j)
      → (∀ x → Φ s x ≡ ψ ℓ b j w β x) → (∀ t → ap K t ≡ app Kc t)
      → LowAt b w β Kc (D s)
    sys→LowAt ks s K bd b w β Kc eΦ ec {a} {x} d r =
      subst (λ o → R j (app Kc a) o) (eΦ x) (subst (λ u → R j u (Φ s x)) (ec a) (ks s K bd d r))
```

旧的三份 `sys→low` (`FI.Suff`, `BL.SuffR`, `QD.SuffRD`; `SuffRA`, `SuffRAD` 是重新导出) 都是 `sys→LowAt` 在各自 `keepAll` 上的取值 (各层良基 `wfAll` 作前提): 旧定理落到新接口的一点 (`fi-low` 等), 同一结论由 `sys→LowAt` 重新得到 (`fi-low′` 等). `QD.SuffD.keepAllᴰ` 是带域的 `KeepSys` (`qd-keep`).

```agda
module MIFI {𝔹 : Block} {𝔽 : Fold 𝔹} {ℜ : Rows 𝔹 𝔽} {𝕋 : Ref} {𝕍 : Val}
            (𝔾 : Graded 𝔹 𝔽 ℜ 𝕋 𝕍) (𝔻 : Doms 𝔹 𝔽) where
  open Laws 𝔾 𝔻
  open FI 𝔾 𝔻
  open BL 𝔾 𝔻
  open QD 𝔾 𝔻
  open MI 𝔾 𝔻

  module FIs {j : Lv} (𝒮 : Sys j) (wfAll : ∀ a → WfL a) (Le : T → T → Set) (wk : Weak) (lm : Lim) (nod : Node)
      (mono : Sys.Monoˢ 𝒮) (𝓀 : Sys.KeepLaw 𝒮) where
    open Sys 𝒮

    module _ (𝒻 : FallLaw) (ex : Out Le 𝓀 𝒻) (gen : ∀ a → Gen⁺ Le a) where
      fi-keep : KeepSys 𝒮 (λ _ → ⊤ᴰ)
      fi-keep {a} s K bd _ r = Suff.keepAll Le wk lm nod mono 𝓀 𝒻 ex gen (wfAll a) s K bd r

      fi-low fi-low′ : ∀ {ℓ} (s : St ℓ) K → Bdˢ s K → ∀ b w β Kc
        → (∀ x → Φ s x ≡ ψ ℓ b j w β x) → (∀ t → ap K t ≡ app Kc t) → LowAt b w β Kc ⊤ᴰ
      fi-low {ℓ} s K bd b w β Kc eΦ ec _ r = Suff.sys→low Le wk lm nod mono 𝓀 𝒻 ex gen (wfAll ℓ) s K bd b w β Kc eΦ ec r
      fi-low′ = sys→LowAt 𝒮 fi-keep

    module _ (𝒻 : FallLaw) (𝒟 : Dom 𝒮)
        (dch : ∀ {a} (s : St a) c x y → Dom.D 𝒟 s (up x c y) → Dom.D 𝒟 (FallLaw.step 𝒻 s c x) (chT a c y))
        (ex : OutD 𝒮 Le 𝓀 𝒻 (Dom.D 𝒟)) (gen : ∀ a → Gen⁺ Le a) where
      qd-keep : KeepSys 𝒮 (Dom.D 𝒟)
      qd-keep {a} s K bd d r = SuffD.keepAllᴰ 𝒮 Le wk lm nod mono 𝓀 𝒻 𝒟 dch ex gen (wfAll a) s K bd r d

  module RDs {j : Lv} (𝒮 𝒜 : Sys j) (𝓀ᴬ : Sys.KeepLaw 𝒜) (ℯ : EmbLaw 𝒮 𝒜 𝓀ᴬ) (wfAll : ∀ a → WfL a)
      (Le : T → T → Set) (wk : Weak) (lm : Lim) (nod : Node) (mono : Sys.Monoˢ 𝒮) (𝓀 : Sys.KeepLaw 𝒮)
      (gen : ∀ a → Gen⁺ Le a) where
    open Sys 𝒮

    module _ (ex : OutR 𝒮 𝒜 𝓀ᴬ ℯ Le 𝓀)
        (auxK : ∀ {b} (s′ : Sys.St 𝒜 b) K″ → Sys.Bdˢ 𝒜 s′ K″ → ∀ {u x} → R b u x → Sys.Q 𝒜 s′ K″ u x) where
      bl-keep : KeepSys 𝒮 (λ _ → ⊤ᴰ)
      bl-keep {a} s K bd _ r = SuffR.keepAll 𝒮 𝒜 𝓀ᴬ ℯ Le wk lm nod mono 𝓀 ex auxK gen (wfAll a) s K bd r

      bl-low bl-low′ : ∀ {ℓ} (s : St ℓ) K → Bdˢ s K → ∀ b w β Kc
        → (∀ x → Φ s x ≡ ψ ℓ b j w β x) → (∀ t → ap K t ≡ app Kc t) → LowAt b w β Kc ⊤ᴰ
      bl-low {ℓ} s K bd b w β Kc eΦ ec _ r =
        SuffR.sys→low 𝒮 𝒜 𝓀ᴬ ℯ Le wk lm nod mono 𝓀 ex auxK gen (wfAll ℓ) s K bd b w β Kc eΦ ec r
      bl-low′ = sys→LowAt 𝒮 bl-keep

    module _ (𝒟 : Dom 𝒮) (Dᴬ : ∀ {a} → Sys.St 𝒜 a → Tr a → Set)
        (rowD : ∀ {a} (s : St a) → RowD 𝒮 𝒜 𝓀ᴬ ℯ (Dom.D 𝒟) Dᴬ s (EmbLaw.row ℯ s))
        (ex : OutRD 𝒮 𝒜 𝓀ᴬ ℯ Le 𝓀 (Dom.D 𝒟))
        (auxK : ∀ {b} (s′ : Sys.St 𝒜 b) K″ → Sys.Bdˢ 𝒜 s′ K″ → ∀ {u x} → R b u x → Dᴬ s′ x → Sys.Q 𝒜 s′ K″ u x) where
      rd-keep : KeepSys 𝒮 (Dom.D 𝒟)
      rd-keep {a} s K bd d r = SuffRD.keepAllᴰ 𝒮 𝒜 𝓀ᴬ ℯ Le wk lm nod mono 𝓀 𝒟 Dᴬ rowD ex auxK gen (wfAll a) s K bd r d

      rd-low rd-low′ : ∀ {ℓ} (s : St ℓ) K → Bdˢ s K → ∀ b w β Kc
        → (∀ x → Φ s x ≡ ψ ℓ b j w β x) → (∀ t → ap K t ≡ app Kc t) → LowAt b w β Kc (Dom.D 𝒟 s)
      rd-low {ℓ} s K bd b w β Kc eΦ ec d r =
        SuffRD.sys→lowᴰ 𝒮 𝒜 𝓀ᴬ ℯ Le wk lm nod mono 𝓀 𝒟 Dᴬ rowD ex auxK gen (wfAll ℓ) s K bd b w β Kc eΦ ec d r
      rd-low′ = sys→LowAt 𝒮 rd-keep
```
