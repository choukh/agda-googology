# 换基律接进整体接口: 按状态分的嵌入行, 充分性

> 判决: 接口与编译定理, 无前提; 只导入标准库, `YiAbs*` 与 `YiFIIface`, 不读记号. 换基行 (`RebAt`): 嵌入的像不低于换基层号上替身树在辅助系统里的像 (`reb`), 目标是换基层号的字面前缀 (`lw`), 目标层槽位在换基层号里的副本带保留证据并落回原槽位 (`cp`, `cpE`, `cpS`); 每个状态的嵌入行是回退行或换基行 (`EmbLaw`). 替身支配原材料是参照一侧的出口 (`OutR.embE` 的第二分量, 用接口关系 R 与 Le).
> 定理: 保留律 + 嵌入律 + 出口 + 辅助系统上的保持 ⇒ 每个状态上保持 (`SuffR.keepAll`) 与这一点的 `LowKeep` (`sys→low`); 辅助系统的保持由 `YiFIIface` 的充分性给出 (`SuffRA`). `YiFIIface` 的回退律是每行都回退的嵌入律 (`fall→emb`, `out→outR`).
> 不给出什么: 不构造关系, 出口是前提; 不说替身是否存在. 实例在 [YiBLFold](YiBLFold.lagda.md), 配对否定在 [YiBLNeg](YiBLNeg.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBLIface where

open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGRow
open import OCF.Lean.YiFIIface

module BL {𝔹 : Block} {𝔽 : Fold 𝔹} {ℜ : Rows 𝔹 𝔽} {𝕋 : Ref} {𝕍 : Val}
          (𝔾 : Graded 𝔹 𝔽 ℜ 𝕋 𝕍) (𝔻 : Doms 𝔹 𝔽) where
  open Laws 𝔾 𝔻
  open Row 𝔾 𝔻
  open FI 𝔾 𝔻
```

## 两个系统与嵌入行

𝒮 是折叠本身, 𝒜 是辅助系统 (换基之后的折叠), 目标同为 j. 换基行的替身 `sub c x` 不依赖原材料 y; 律里只出现一个孩子下标 c. 成对出现的是目标 j 与换基层号 (字面路径 `lw`), 目标层槽位 q 与它的副本 (`cp`).

```agda
  module _ {j : Lv} (𝒮 𝒜 : Sys j) (𝓀ᴬ : Sys.KeepLaw 𝒜) where
    private
      module S  = Sys 𝒮
      module A  = Sys 𝒜
      module KA = Sys.KeepLaw 𝓀ᴬ

    record RebAt {a : Lv} (s : S.St a) : Set where
      field
        Lr  : Ch a → Tr a → Lv
        Sr  : (c : Ch a) (x : Tr a) → A.St (Lr c x)
        sub : (c : Ch a) (x : Tr a) → Tr (Lr c x)
        reb : (c : Ch a) (x : Tr a) (y : ChT a c) → A.Φ (Sr c x) (sub c x) ⊴ S.Φ s (up x c y)
        lw  : (c : Ch a) (x : Tr a) → j ⊑ Lr c x
        cp  : (c : Ch a) (x : Tr a) → Sl j → Sl (Lr c x)
        cpE : (c : Ch a) (x : Tr a) (q : Sl j) → A.Ev (Sr c x) (cp c x q)
        cpS : (c : Ch a) (x : Tr a) (q : Sl j) → KA.slot (Sr c x) (cp c x q) (cpE c x q) ≡ q

    record FallAt {a : Lv} (s : S.St a) : Set where
      field
        step : (c : Ch a) → Tr a → S.St (chL a c)
        fall : (c : Ch a) (x : Tr a) (y : ChT a c) → S.Φ (step c x) (chT a c y) ⊴ S.Φ s (up x c y)

    record EmbLaw : Set where
      field
        row : ∀ {a} (s : S.St a) → FallAt s ⊎ RebAt s
```

## 出口

回退行的出口同 `Out.upE`. 换基行两条: 上下文交给替身的状态 (同 `upE` 的形状, 对一切孩子一致); 替身支配原材料: 原材料下面的参照项 u 换成替身下面的 u″, 且 t ⊕ u 沿 Le 不高于 t ⊕ u″. 其余五条与 `Out` 逐字相同 (`out→outR` 核对).

```agda
    module _ (ℯ : EmbLaw) where
      open EmbLaw ℯ

      EmbOut : (Le : T → T → Set) → ∀ {a} (s : S.St a) → S.Cxt → FallAt s ⊎ RebAt s → Set
      EmbOut Le {a} s K (inj₁ f) = (c : Ch a) → ∀ {t x} → R a t x → S.Q s K t x
        → Σ S.Cxt λ K′ → S.Bdˢ (FallAt.step f c x) K′ × (∀ u → S.ap K′ u ≡ S.ap K (t ⊕ u))
      EmbOut Le {a} s K (inj₂ r) =
          ((c : Ch a) → ∀ {t x} → R a t x → S.Q s K t x
            → Σ A.Cxt λ K″ → A.Bdˢ (RebAt.Sr r c x) K″ × (∀ u → A.ap K″ u ≡ S.ap K (t ⊕ u)))
        × ((c : Ch a) → ∀ {t u x} (y : ChT a c) → R a t x → R (chL a c) u (chT a c y)
            → Σ T λ u″ → R (RebAt.Lr r c x) u″ (RebAt.sub r c x) × Le (t ⊕ u) (t ⊕ u″))

      record OutR (Le : T → T → Set) (𝓀 : S.KeepLaw) : Set where
        open S.KeepLaw 𝓀
        field
          zeroE : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t x} → C0 t → S.Q s K t x
          succE : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t x} → C1 t → R a (pred t) x → S.Q s K (pred t) x → S.Q s K t (sc x)
          limE  : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t} → Cω t → Cω (S.ap K t) × (∀ n → fsn (S.ap K t) n ≡ S.ap K (fsn t n))
          leE   : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {u t o} → Le u t → R j (S.ap K t) o → R j (S.ap K u) o
          nodeE : ∀ {a} (s : S.St a) K → S.Bdˢ s K → (p : Sl a) → ∀ {t κ} (g : SlT a p → Tr a) → CΩ t κ → Nu a p κ
                → (∀ η c → R (slL a p) η (slT a p c) → R a (fsT t η) (g c))
                → (Σ (S.Ev s p) λ e → CΩ (S.ap K t) κ × (∀ η → fsT (S.ap K t) η ≡ S.ap K (fsT t η))
                     × Nu j (slot s p e) κ
                     × (∀ η c → R (slL j (slot s p e)) η (slT j (slot s p e) c) → R (slL a p) η (slT a p (mvc s p e c))))
                  ⊎ (Σ (ℕ → T) λ γ → Σ (ℕ → SlT a p) λ z → Cω (S.ap K t) × (∀ k → fsn (S.ap K t) k ≡ S.ap K (fsT t (γ k)))
                     × (∀ k → R (slL a p) (γ k) (slT a p (z k))) × (∀ k → S.Φ s (g (z k)) ⊴ S.Φ s (nd p g)))
          embE  : ∀ {a} (s : S.St a) K → S.Bdˢ s K → EmbOut Le s K (row s)
```

## 充分性

同 `Suff.keepAll` 对 `WfL` 递归; 回退行用孩子层的结论, 换基行用辅助系统上的保持 `auxK` (换基层号不是孩子, 不进本系统的递归).

```agda
      module SuffR (Le : T → T → Set) (wk : Weak) (lm : Lim) (nod : Node) (mono : S.Monoˢ)
                   (𝓀 : S.KeepLaw) (ex : OutR Le 𝓀)
                   (auxK : ∀ {b} (s′ : A.St b) K″ → A.Bdˢ s′ K″ → ∀ {u x} → R b u x → A.Q s′ K″ u x)
                   (gen : ∀ a → Gen⁺ Le a) where
        open S.KeepLaw 𝓀
        open OutR ex

        rules : ∀ {a} → (∀ c (s′ : S.St (chL a c)) K′ → S.Bdˢ s′ K′ → ∀ {t x} → R (chL a c) t x → S.Q s′ K′ t x)
              → (s : S.St a) (K : S.Cxt) → S.Bdˢ s K → Rules a (S.Q s K)
        rules {a} child s K bd = record
          { qz = zeroE s K bd
          ; q1 = succE s K bd
          ; qL = λ {t} {x} e _ h → lm (proj₁ (limE s K bd e))
                   (λ n → subst (λ u → R j u (S.Φ s x)) (sym (proj₂ (limE s K bd e) n)) (h n))
          ; qΩ = node
          ; qU = emb
          ; qw = λ _ q d → wk q (mono s d) }
          where
          node : (p : Sl a) {t κ : T} (g : SlT a p → Tr a) → CΩ t κ → Nu a p κ
               → (∀ η c → R (slL a p) η (slT a p c) → R a (fsT t η) (g c))
               → (∀ η c → R (slL a p) η (slT a p c) → S.Q s K (fsT t η) (g c)) → S.Q s K t (nd p g)
          node p g e nu hR hQ with nodeE s K bd p g e nu hR
          ... | inj₁ (ev , cΩ , fs , nu′ , tr) = wk⊴ wk
            (nod (slot s p ev) (λ c → S.Φ s (g (mvc s p ev c))) cΩ nu′
              (λ η c l → subst (λ o → R j o (S.Φ s (g (mvc s p ev c)))) (sym (fs η)) (hQ η (mvc s p ev c) (tr η c l))))
            (keep s p ev g)
          ... | inj₂ (γ , z , cω , fs , ch , tr) =
            lm cω (λ k → subst (λ o → R j o (S.Φ s (nd p g))) (sym (fs k)) (wk⊴ wk (hQ (γ k) (z k) (ch k)) (tr k)))

          emb : (c : Ch a) {t u : T} {x : Tr a} (y : ChT a c) → R a t x → S.Q s K t x → R (chL a c) u (chT a c y)
              → S.Q s K (t ⊕ u) (up x c y)
          emb c {t} {u} {x} y r q ry with row s | embE s K bd
          ... | inj₁ f | E with E c r q
          ...   | K′ , bd′ , eq = wk⊴ wk
            (subst (λ o → R j o (S.Φ (FallAt.step f c x) (chT a c y))) (eq u) (child c (FallAt.step f c x) K′ bd′ ry))
            (FallAt.fall f c x y)
          emb c {t} {u} {x} y r q ry | inj₂ rw | (E₁ , E₂) with E₁ c r q | E₂ c y r ry
          ...   | K″ , bd″ , eq | u″ , rs , le = leE s K bd le
            (subst (λ o → R j o (S.Φ s (up x c y))) (eq u″)
              (wk⊴ wk (auxK (RebAt.Sr rw c x) K″ bd″ rs) (RebAt.reb rw c x y)))

        keepAll : ∀ {a} → WfL a → (s : S.St a) (K : S.Cxt) → S.Bdˢ s K → ∀ {t x} → R a t x → S.Q s K t x
        keepAll {a} (wf f) s K bd =
          gen a (S.Q s K) (rules (λ c s′ K′ bd′ → keepAll (f c) s′ K′ bd′) s K bd) (λ le _ q → leE s K bd le q)

        sys→low : ∀ {ℓ} → WfL ℓ → (s : S.St ℓ) (K : S.Cxt) → S.Bdˢ s K → (b : Bs ℓ) (w : j ⊑ ℓ) (β : Bt j) (Kc : Cx ℓ j)
          → (∀ x → S.Φ s x ≡ ψ ℓ b j w β x) → (∀ t → S.ap K t ≡ app Kc t)
          → ∀ {a x} → R ℓ a x → R j (app Kc a) (ψ ℓ b j w β x)
        sys→low W s K bd b w β Kc eΦ ec {a} {x} r =
          subst (λ o → R j (app Kc a) o) (eΦ x) (subst (λ u → R j u (S.Φ s x)) (ec a) (keepAll W s K bd r))
```

辅助系统 𝒜 自己满足 `YiFIIface` 的两条律与出口, 各层良基, 则 `auxK` 由 `Suff.keepAll` 给出.

```agda
      module SuffRA (Le : T → T → Set) (wk : Weak) (lm : Lim) (nod : Node) (mono : S.Monoˢ)
                    (𝓀 : S.KeepLaw) (ex : OutR Le 𝓀)
                    (monoᴬ : A.Monoˢ) (𝒻ᴬ : A.FallLaw) (exᴬ : A.Out Le 𝓀ᴬ 𝒻ᴬ) (wfAll : ∀ b → WfL b)
                    (gen : ∀ a → Gen⁺ Le a) where
        private module SA = A.Suff Le wk lm nod monoᴬ 𝓀ᴬ 𝒻ᴬ exᴬ gen
        open SuffR Le wk lm nod mono 𝓀 ex (λ {b} s′ → SA.keepAll (wfAll b) s′) gen public
```

## 回退律是特例

每个状态都是回退行时, `Out` 给出 `OutR`; 于是 `Suff` 的前提给出 `SuffRA` 的前提 (𝒜 取 𝒮).

```agda
    fall→emb : S.FallLaw → EmbLaw
    fall→emb 𝒻 = record { row = λ s → inj₁ (record { step = S.FallLaw.step 𝒻 s ; fall = S.FallLaw.fall 𝒻 s }) }

    out→outR : ∀ {Le 𝓀 𝒻} → S.Out Le 𝓀 𝒻 → OutR (fall→emb 𝒻) Le 𝓀
    out→outR ex = record
      { zeroE = S.Out.zeroE ex ; succE = S.Out.succE ex ; limE = S.Out.limE ex ; leE = S.Out.leE ex
      ; nodeE = S.Out.nodeE ex ; embE = λ s K bd c r q → S.Out.upE ex s K bd c r q }
```
