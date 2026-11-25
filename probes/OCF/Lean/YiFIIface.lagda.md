# 对折叠参数化的整体接口: 保留律, 回退律, 充分性

> 判决: 接口与编译定理, 无前提; 只导入标准库与 `YiAbs*`, 不读记号. 固定目标 j 的 "折叠像系统" `Sys` (状态, 像 `Φ`, 字面证据 `Ev`; 参照一侧的上下文 `Cxt` 与状态对上下文的条件 `Bdˢ`); 树一侧两条律 `KeepLaw` (有字面证据的槽位保留, 即 `row-node-keep` 的树一侧), `FallLaw` (嵌入的像不低于孩子材料在同一系统里朝同一目标的像, 即 `row-up` 换成不指定孩子的写法); 出口 `Out` 是参照一侧的条件.
> 定理: 两条律加出口, 层号沿孩子良基, 各层的关系是生成的, 则每个状态上保持成立 (`keep`), 状态对上折叠时得到这一点上的 `LowKeep` (`sys→low`). 配对否定: 参照一侧保留余尾 Ω 而像不含结点, 这个状态上保持不成立 (`nokeep→¬`, 用 `YiAbsGNeg.Inv.inv`).
> 不给出什么: 不构造关系; 出口里 "参照保留的槽位都有字面证据" 是前提, 不是定理; 对角一支的链是前提. 具体折叠的树一侧实例在 [YiFIFold](YiFIFold.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFIIface where

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGRow
open import OCF.Lean.YiAbsGNeg

module FI {𝔹 : Block} {𝔽 : Fold 𝔹} {ℜ : Rows 𝔹 𝔽} {𝕋 : Ref} {𝕍 : Val}
          (𝔾 : Graded 𝔹 𝔽 ℜ 𝕋 𝕍) (𝔻 : Doms 𝔹 𝔽) where
  open Laws 𝔾 𝔻
  open Row 𝔾 𝔻
  open Neg 𝔾 𝔻 using (module Inv)
```

## 良基与生成

`WfL a`: 层号 a 沿孩子良基 (具体块里层号是归纳类型, 对一切层号成立). `Gen⁺ Le a`: 六条规则之外多一条参照一侧沿 `Le` 的向下封闭; 主线的关系有这第七条 (`YiHCRel.mc`), `Le` 取空就是 `Gen`.

```agda
  data WfL (a : Lv) : Set where
    wf : ((c : Ch a) → WfL (chL a c)) → WfL a

  Gen⁺ : (T → T → Set) → Lv → Set₁
  Gen⁺ Le a = (Q : T → Tr a → Set) → Rules a Q
    → (∀ {s t x} → Le s t → R a t x → Q t x → Q s x) → ∀ {t x} → R a t x → Q t x

  gen→gen⁺ : ∀ {Le a} → Gen a → Gen⁺ Le a
  gen→gen⁺ G Q rs _ = G Q rs
```

## 系统

`St a`: 第 a 层上的状态 (具体折叠里是底, 底值, 路径, 或回退之后的下行链与前缀的折叠). `Φ s x`: 树 x 在状态 s 下朝 j 的像. `Ev s p`: 槽位 p 在状态 s 下保留的字面证据 (例如槽位层号到 j 的一条字面路径). 参照一侧: 上下文 `Cxt` 与它的作用 `ap`; `Bdˢ s K`: 状态 s 对着上下文 K (同 `Graded.Bd`). 两条树一侧的律不提参照一侧.

```agda
  record Sys (j : Lv) : Set₁ where
    field
      St  : Lv → Set
      Φ   : ∀ {a} → St a → Tr a → Tr j
      Ev  : ∀ {a} → St a → Sl a → Set
      Cxt : Set
      ap  : Cxt → T → T
      Bdˢ : ∀ {a} → St a → Cxt → Set

    Q : ∀ {a} → St a → Cxt → T → Tr a → Set
    Q s K t x = R j (ap K t) (Φ s x)
```

保留律: 证据给出目标层的槽位与分支下标的换型, 结点的像不低于逐分支取像的结点. 律里只出现一个槽位, 不出现孩子下标.

```agda
    record KeepLaw : Set where
      field
        slot : ∀ {a} (s : St a) (p : Sl a) → Ev s p → Sl j
        mvc  : ∀ {a} (s : St a) (p : Sl a) (e : Ev s p) → SlT j (slot s p e) → SlT a p
        keep : ∀ {a} (s : St a) (p : Sl a) (e : Ev s p) (g : SlT a p → Tr a)
             → nd (slot s p e) (λ c → Φ s (g (mvc s p e c))) ⊴ Φ s (nd p g)
```

回退律: 嵌入 `up x c y` 的像不低于孩子材料 y 在孩子层状态 `step s c x` 下的像. 孩子层的状态仍在同一个系统里, 目标仍是 j, 所以保留律对孩子里的槽位照样适用; 律对一切孩子 c 一致, 不比较 c 与目标所在的孩子.

```agda
    record FallLaw : Set where
      field
        step : ∀ {a} → St a → (c : Ch a) → Tr a → St (chL a c)
        fall : ∀ {a} (s : St a) (c : Ch a) (x : Tr a) (y : ChT a c)
             → Φ (step s c x) (chT a c y) ⊴ Φ s (up x c y)

    Monoˢ : Set
    Monoˢ = ∀ {a} (s : St a) {x y : Tr a} → x ◃ y → Φ s x ◃ Φ s y
```

出口 (参照一侧), 都在 `Bdˢ s K` 之下: 零行, 后继行 (同 `YiAbsGRow`, 作前提), ℕ 极限穿过上下文, 嵌入处上下文与条件的交接 (同 `row-up` 的 `bstep`), 沿 `Le` 向下. 结点处二选一: 上下文保持余尾 Ω, 此时要字面证据, 余尾下标与分支关系沿换型搬运; 或上下文把余尾降成 ω, 此时要回灌链 (同 `row-node-diag`).

```agda
    record Out (Le : T → T → Set) (𝓀 : KeepLaw) (𝒻 : FallLaw) : Set where
      open KeepLaw 𝓀
      open FallLaw 𝒻
      field
        zeroE : ∀ {a} (s : St a) K → Bdˢ s K → ∀ {t x} → C0 t → Q s K t x
        succE : ∀ {a} (s : St a) K → Bdˢ s K → ∀ {t x} → C1 t → R a (pred t) x → Q s K (pred t) x → Q s K t (sc x)
        limE  : ∀ {a} (s : St a) K → Bdˢ s K → ∀ {t} → Cω t → Cω (ap K t) × (∀ n → fsn (ap K t) n ≡ ap K (fsn t n))
        upE   : ∀ {a} (s : St a) K → Bdˢ s K → (c : Ch a) → ∀ {t x} → R a t x → Q s K t x
              → Σ Cxt λ K′ → Bdˢ (step s c x) K′ × (∀ u → ap K′ u ≡ ap K (t ⊕ u))
        leE   : ∀ {a} (s : St a) K → Bdˢ s K → ∀ {u t o} → Le u t → R j (ap K t) o → R j (ap K u) o
        nodeE : ∀ {a} (s : St a) K → Bdˢ s K → (p : Sl a) → ∀ {t κ} (g : SlT a p → Tr a) → CΩ t κ → Nu a p κ
              → (∀ η c → R (slL a p) η (slT a p c) → R a (fsT t η) (g c))
              → (Σ (Ev s p) λ e → CΩ (ap K t) κ × (∀ η → fsT (ap K t) η ≡ ap K (fsT t η))
                   × Nu j (slot s p e) κ
                   × (∀ η c → R (slL j (slot s p e)) η (slT j (slot s p e) c) → R (slL a p) η (slT a p (mvc s p e c))))
              ⊎ (Σ (ℕ → T) λ γ → Σ (ℕ → SlT a p) λ z → Cω (ap K t) × (∀ k → fsn (ap K t) k ≡ ap K (fsT t (γ k)))
                   × (∀ k → R (slL a p) (γ k) (slT a p (z k))) × (∀ k → Φ s (g (z k)) ⊴ Φ s (nd p g)))
```

## 充分性

对 `WfL` 递归: 第 a 层用生成原理, 嵌入一行用孩子层的结论.

```agda
    module Suff (Le : T → T → Set) (wk : Weak) (lm : Lim) (nod : Node) (mono : Monoˢ)
                (𝓀 : KeepLaw) (𝒻 : FallLaw) (ex : Out Le 𝓀 𝒻) (gen : ∀ a → Gen⁺ Le a) where
      open KeepLaw 𝓀
      open FallLaw 𝒻
      open Out ex

      rules : ∀ {a} → (∀ c (s′ : St (chL a c)) K′ → Bdˢ s′ K′ → ∀ {t x} → R (chL a c) t x → Q s′ K′ t x)
            → (s : St a) (K : Cxt) → Bdˢ s K → Rules a (Q s K)
      rules {a} child s K bd = record
        { qz = zeroE s K bd
        ; q1 = succE s K bd
        ; qL = λ {t} {x} e _ h → lm (proj₁ (limE s K bd e))
                 (λ n → subst (λ u → R j u (Φ s x)) (sym (proj₂ (limE s K bd e) n)) (h n))
        ; qΩ = node
        ; qU = emb
        ; qw = λ _ q d → wk q (mono s d) }
        where
        node : (p : Sl a) {t κ : T} (g : SlT a p → Tr a) → CΩ t κ → Nu a p κ
             → (∀ η c → R (slL a p) η (slT a p c) → R a (fsT t η) (g c))
             → (∀ η c → R (slL a p) η (slT a p c) → Q s K (fsT t η) (g c)) → Q s K t (nd p g)
        node p g e nu hR hQ with nodeE s K bd p g e nu hR
        ... | inj₁ (ev , cΩ , fs , nu′ , tr) = wk⊴ wk
          (nod (slot s p ev) (λ c → Φ s (g (mvc s p ev c))) cΩ nu′
            (λ η c l → subst (λ o → R j o (Φ s (g (mvc s p ev c)))) (sym (fs η)) (hQ η (mvc s p ev c) (tr η c l))))
          (keep s p ev g)
        ... | inj₂ (γ , z , cω , fs , ch , tr) =
          lm cω (λ k → subst (λ o → R j o (Φ s (nd p g))) (sym (fs k)) (wk⊴ wk (hQ (γ k) (z k) (ch k)) (tr k)))

        emb : (c : Ch a) {t u : T} {x : Tr a} (y : ChT a c) → R a t x → Q s K t x → R (chL a c) u (chT a c y)
            → Q s K (t ⊕ u) (up x c y)
        emb c {t} {u} {x} y r q ry with upE s K bd c r q
        ... | K′ , bd′ , eq = wk⊴ wk
          (subst (λ o → R j o (Φ (step s c x) (chT a c y))) (eq u) (child c (step s c x) K′ bd′ ry))
          (fall s c x y)

      keepAll : ∀ {a} → WfL a → (s : St a) (K : Cxt) → Bdˢ s K → ∀ {t x} → R a t x → Q s K t x
      keepAll {a} (wf f) s K bd =
        gen a (Q s K) (rules (λ c s′ K′ bd′ → keepAll (f c) s′ K′ bd′) s K bd) (λ le _ q → leE s K bd le q)
```

状态对上折叠 `ψ ℓ b j w β`, 上下文对上 `app Kc`: 得到这一点上折到低层的保持, 对第 ℓ 层的一切树 (不限 `Gx`).

```agda
      sys→low : ∀ {ℓ} → WfL ℓ → (s : St ℓ) (K : Cxt) → Bdˢ s K → (b : Bs ℓ) (w : j ⊑ ℓ) (β : Bt j) (Kc : Cx ℓ j)
        → (∀ x → Φ s x ≡ ψ ℓ b j w β x) → (∀ t → ap K t ≡ app Kc t)
        → ∀ {a x} → R ℓ a x → R j (app Kc a) (ψ ℓ b j w β x)
      sys→low W s K bd b w β Kc eΦ ec {a} {x} r =
        subst (λ o → R j (app Kc a) o) (eΦ x) (subst (λ u → R j u (Φ s x)) (ec a) (keepAll W s K bd r))
```

## 配对否定

`H o`: 树 o 含结点 (同 `YiAbsGNeg.Inv` 的前提). 目标层的关系由六条生成时, 参照一侧保持余尾 Ω 而像不含结点, 这个状态上的保持不成立; 于是这一点上两条律与出口不能同时成立 (`laws→¬`). 否定的是接口上的保持, 不经过值.

```agda
    module NoKeep (G : Gen j) (κ : T) (H : Tr j → Set)
        (d0 : ∀ {s} → C0 s → CΩ s κ → ⊥) (d1 : ∀ {s} → C1 s → CΩ s κ → ⊥) (dω : ∀ {s} → Cω s → CΩ s κ → ⊥)
        (hΩ : (p : Sl j) (g : SlT j p → Tr j) → H (nd p g))
        (hw : ∀ {x x′} → H x → x ◃ x′ → H x′)
        (hU : (c : Ch j) {t s : T} {x : Tr j} (y : ChT j c) → CΩ (t ⊕ s) κ → (CΩ t κ → H x)
            → R (chL j c) s (chT j c y) → H (up x c y)) where

      nokeep→¬ : ∀ {a} (s : St a) (K : Cxt) {t x} → CΩ (ap K t) κ → (H (Φ s x) → ⊥) → Q s K t x → ⊥
      nokeep→¬ s K e no q = no (Inv.inv G κ H d0 d1 dω hΩ hw hU q e)

      laws→¬ : ∀ {Le} (wk : Weak) (lm : Lim) (nod : Node) (mono : Monoˢ) (𝓀 : KeepLaw) (𝒻 : FallLaw)
        → Out Le 𝓀 𝒻 → (∀ a → Gen⁺ Le a)
        → ∀ {a} → WfL a → (s : St a) (K : Cxt) → Bdˢ s K → {t : T} {x : Tr a} → R a t x
        → CΩ (ap K t) κ → (H (Φ s x) → ⊥) → ⊥
      laws→¬ {Le} wk lm nod mono 𝓀 𝒻 ex gen W s K bd r e no =
        nokeep→¬ s K e no (Suff.keepAll Le wk lm nod mono 𝓀 𝒻 ex gen W s K bd r)
```
