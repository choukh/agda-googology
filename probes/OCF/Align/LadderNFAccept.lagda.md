# 阶梯去记号: 验收

> **验收文件, 不在证书的闭包内.** 记号与标签只在这里出现 (与它导入的标签阶梯). 结论写在 [LadderNF](LadderNF.lagda.md).
>
> 主线 (`LadderNFTree`, 基于 `OCF.Free.*`) 与标签阶梯 (`ScafLadderQ`, 基于 `ScafLadderZ*`) 是两个世界: 树的代码逐字相同 (`LadderNFTree` §1 起与 `ScafLadderQ` 字面一致, 脚本比较), 类型不是同一个. 所以这里用**另一个方向**的重新检查: 证书 `LadderNF*` 只改导入, 克隆成 `LadderNFW*`, 落在标签阶梯的树上. 克隆是脚本生成的, 代码行逐字.
>
> 1. **`label-cert`: 证书的计值带已有的标签.** `Lab (forceᴺ _ (GᴺTᵠ m α ev z)) (ψ₀(Ω_{Ω·(m+1)+θ}))`, 对一切 $m$, 一切 $\theta<\psi_0(\Omega_{\Omega\cdot(m+2)})$, 经 `ofL`, `forceᴺ-≅`, `Lab-≅`. 证书是 `LadderNFW` 世界里的 `GᴺTᵠ`, 它的证明不读标签 (切片与闭包在主线版本上做).
> 2. **实例.** `anchor-Ω₂` ($\psi_0(\Omega_{\Omega\cdot2})$), `label-Ω·2+1`, `label-Ω·3`, `label-Ω·`.
> 3. **`agree-P`: 与旧树 `Tᴾ` 经标签 $\cong$** (`Lab-uniq`), 在 $\theta$ 处, 所以 $\psi_0(\Omega_{\Omega\cdot2})$ 确实是原来的那一个.
> 4. **`Tω-via-labels`: $T_\omega$ 的 `Goodᴺ` 与标签.** 单调来自 `Tω-label`, 读记号. 所以这条**不是**记号无关的证书, 只说明 `GᴺTω-if` 的前提为真. 记号无关的单调没有证到.
>
> 5. **有限测试 (§5):** `fgh-Ω·2`, `fgh-Ω·3`: 两个世界的 FGH 在第 0 项相等, `refl`. 不是证明.
>
> **没有做到的.** 这里没有跨世界的桥: 主线的 `GᴺTᵠ` 与 `LadderNFW` 的 `GᴺTᵠ` 不是同一个项, 标签贴的是后者. 两者的代码逐字相同, 这是脚本比较, 不是定理. `OCF.Free.Lab` 的做法 (把标签链搬到主线的定义上) 对这条标签链要克隆约 60 个模块, 没有做.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderNFAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.Level
open import OCF.Align.ScafLadderZPrefix using (Z; ĉᴸ; toZ)
open import OCF.Align.Correspond using (Lab; Lab-≅; l0; lω)
open import OCF.Align.Stage2 using (Lab-uniq)
open import OCF.Align.ScafLadderZUniform3Base using (Ev; Lab₀)
open import OCF.Align.ScafLadderZUniform4Base using (Fl)
open import OCF.Align.ScafLadderZStandardOmega using (NF₁; n[])
import OCF.Align.ScafLadderZGoodLBase as GL
open GL using (Goodᴸ; forceᴸ; forceᴸ-HS; Ptᴸ; ptsᴸ; lvᴸ)
import OCF.Align.EBO as E
open E using (T; natT; Ωt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.ScafLadderQClass using (Ωᵉ)
open import OCF.Align.ScafLadderZUniform3Base using (ψ₀ᵗ)
open import OCF.Align.ScafLadderQ using (Tᵠ; Tω; Tωn; ok₀)
open import OCF.Align.ScafLadderQTop using (TΩᵠ-label; TΩ·-label; TΩ·+1-label; Tω-label; B; Tn-label; nf-n; mono-n; tω)
open import OCF.Align.ScafLadderZStage2Label using (Lab-oc)
open import OCF.Align.Stage2 using () renaming (≺→⊑ to ≺→⊑²)
open import OCF.Align.ScafLadderTop using (TΩ₂-label)
open import OCF.Align.ScafLadderTree using (Tᴾ)
-- 克隆的证书
open import OCF.Align.LadderNFWForce
open import OCF.Align.LadderNFWEq using (_≅ᶻ_; toZ-≅; lᶻ)
open import OCF.Align.LadderNFWFloor using (∼ᶠ-refl)
open import OCF.Align.LadderNFWMain using (GᴺTᵠ; GᴺTωn; GᴺTω-if)
open import OCF.Align.LadderNFWRel using (R→≈ᵠ; RΩ̇; rs; rz)
```

## §1 遗忘标签

与 [NotFree](NotFree.lagda.md) §3 同形, 证书是标签阶梯世界的 `Goodᴸ`.

```agda
ofL   : ∀ {x} → Goodᴸ x → Goodᴺ x
ofL-≅ : ∀ {x} (G : Goodᴸ x) → forceᴺ x (ofL G) ≅ forceᴸ x G

ofL GL.gz = gz
ofL (GL.gs G) = gs (ofL G)
ofL (GL.gl G st) = gl (λ n → ofL (G n))
  (λ n → ⊑-trans (≅→⊑ (ofL-≅ (G n))) (⊑-trans (st n) (≅→⊑ (≅-sym (ofL-≅ (G (suc n)))))))
ofL {ĉᴸ c t₀ g o₀ o} (GL.gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) =
  gc (λ m → Ptᴸ.x (P m)) (λ m → Ptᴸ.hx (P m)) (λ m → Ptᴸ.dx (P m))
     (ofL G₀) (ofL-≅ G₀) (λ m → ofL (Gm m)) (λ m → ofL-≅ (Gm m))
     (ofL Go₀) (λ k → ofL (Go k))
     (⊑-trans (≅→⊑ (ofL-≅ Go₀)) (⊑-trans mo₀ (≅→⊑ (≅-sym (ofL-≅ (Go 0))))))
     (λ k → ⊑-trans (≅→⊑ (ofL-≅ (Go k))) (⊑-trans (mo k) (≅→⊑ (≅-sym (ofL-≅ (Go (suc k)))))))
  where
  P : ∀ k → Ptᴸ c γ k
  P = ptsᴸ (forceᴸ t₀ G₀) (forceᴸ-HS t₀ G₀) l₀ d₀ (λ m Y hY lY e → forceᴸ _ (Gg m Y hY lY e))
           (λ m Y hY lY e → forceᴸ-HS _ (Gg m Y hY lY e)) lE dE
  Gm : ∀ m → Goodᴸ (g (lvᴸ (P m)) (Ptᴸ.dx (P m)))
  Gm m = Gg m (Ptᴸ.x (P m)) (Ptᴸ.hx (P m)) (Ptᴸ.lx (P m)) (Ptᴸ.dx (P m))

ofL-≅ GL.gz = z≅
ofL-≅ (GL.gs G) = s≅ (ofL-≅ G)
ofL-≅ (GL.gl G st) = l≅ (λ n → ofL-≅ (G n))
ofL-≅ (GL.gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) = l≅ eo
  where
  eo : ∀ n → _
  eo zero    = ofL-≅ Go₀
  eo (suc k) = ofL-≅ (Go k)

-- 同一个 Z 上两个证书的计值互模拟
same : ∀ {x} → x ≅ᶻ x → (G : Goodᴺ x) (L : Goodᴸ x) → forceᴺ x G ≅ forceᴸ x L
same d G L = ≅-trans (forceᴺ-≅ d G (ofL L)) (ofL-≅ L)
```

## §2 标签贴在证书的计值上

```agda
selfT : ∀ m α {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → toZ (Tᵠ m α ev p) ≅ᶻ toZ (Tᵠ m α ev p)
selfT m α ev p = toZ-≅ (R→≈ᵠ (RΩ̇ m (≅ᴵ-refl α)) ok₀ (λ i h r → ok₀ i) ok₀ (λ i h r → ok₀ i) ev p ev p (≅ᴵ-refl zero))

label-cert : ∀ m {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ B m → ∀ {α} → α ≅ᴵ toLevel Y hY →
             ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (GᴺTᵠ m α ev p)) (ψ₀ᵗ (Ωt (Ωᵉ (suc m) θ)))
label-cert m Y hY lY nθ pm {α} e ev p = Lab-≅ (same (selfT m α ev p) (GᴺTᵠ m α ev p) (proj₁ L)) (proj₂ L)
  where L = TΩᵠ-label m Y hY lY nθ pm e ev p

-- ψ₀(Ω_{Ω·(m+1)}), 一切 m
label-Ω· : ∀ m {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (GᴺTᵠ m zero ev p)) (ψ₀ᵗ (Ωt (Ωᵉ (suc m) [])))
label-Ω· m ev p = Lab-≅ (same (selfT m zero ev p) (GᴺTᵠ m zero ev p) (proj₁ L)) (proj₂ L)
  where L = TΩ·-label m ev p

-- 决定性锚点 ψ₀(Ω_{Ω·2})
anchor-Ω₂ : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (GᴺTᵠ 1 zero ev p)) (ψ₀ᵗ (Ωt (Ωᵉ 2 [])))
anchor-Ω₂ = label-Ω· 1

-- ψ₀(Ω_{Ω·3})
label-Ω·3 : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (GᴺTᵠ 2 zero ev p)) (ψ₀ᵗ (Ωt (Ωᵉ 3 [])))
label-Ω·3 = label-Ω· 2

-- ψ₀(Ω_{Ω·(m+1)+1}), 一切 m; m = 1 是 ψ₀(Ω_{Ω·2+1})
label-Ω·+1 : ∀ m {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (GᴺTᵠ m (suc zero) ev p)) (ψ₀ᵗ (Ωt (Ωᵉ (suc m) (natT 1))))
label-Ω·+1 m ev p = Lab-≅ (same (selfT m (suc zero) ev p) (GᴺTᵠ m (suc zero) ev p) (proj₁ L)) (proj₂ L)
  where L = TΩ·+1-label m ev p
```

## §3 与旧树

`TΩ₂-label` 是旧的一层树 `Tᴾ` 上的标签. 两棵树带同一个标签, 所以 $\cong$.

```agda
agree-P : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) (lY : Lab Y θ) (nθ : NF₁ θ) (pm : θ <ᵗ B 1) {ℓ ℓ′} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) (ev′ : Ev ℓ′ Fl) (p′ : zero <ᴵ ℓ′) →
          forceᴺ _ (GᴺTᵠ 1 (toLevel Y hY) ev p) ≅ forceᴸ _ (proj₁ (TΩ₂-label Y hY lY nθ pm (≅ᴵ-refl _) ev′ p′))
agree-P Y hY lY nθ pm ev p ev′ p′ = Lab-uniq (label-cert 1 Y hY lY nθ pm (≅ᴵ-refl _) ev p) (proj₂ (TΩ₂-label Y hY lY nθ pm (≅ᴵ-refl _) ev′ p′))
```

## §4 $\psi_0(\Omega_{\Omega\cdot\omega})$: 单调读记号

`Tω-label` 的证书是 `gl`, 单调来自记号的 `Lab-oc`. 把它搬到逐项的 `GᴺTωn` 上, 就有 `GᴺTω-if` 的前提. 这条不记号无关.

```agda
selfω : ∀ k {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → toZ (Tωn k ev p) ≅ᶻ toZ (Tωn k ev p)
selfω zero ev p = toZ-≅ (R→≈ᵠ (rs (∼ᶠ-refl Fl) (λ i ()) rz) ok₀ (λ i h r → ok₀ i) ok₀ (λ i h r → ok₀ i) ev p ev p (≅ᴵ-refl zero))
selfω (suc k) ev p = selfT k zero ev p

Tω-mono-lab : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) n → forceᴺ _ (GᴺTωn n ev p) ⊑ forceᴺ _ (GᴺTωn (suc n) ev p)
Tω-mono-lab ev p n =
  ⊑-trans (≅→⊑ (same (selfω n ev p) (GᴺTωn n ev p) (proj₁ (Tn-label n ev p))))
    (⊑-trans (≺→⊑² (Lab-oc (proj₂ (Tn-label (suc n) ev p)) (nf-n (suc n)) (proj₂ (Tn-label n ev p)) (nf-n n) (mono-n n)))
             (≅→⊑ (≅-sym (same (selfω (suc n) ev p) (GᴺTωn (suc n) ev p) (proj₁ (Tn-label (suc n) ev p))))))

Tω-via-labels : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Goodᴺ (toZ (Tω ev p))
Tω-via-labels ev p = GᴺTω-if ev p (Tω-mono-lab ev p)

Tω-lab : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (Tω-via-labels ev p)) tω
Tω-lab ev p = Lab-≅ (same (lᶻ (λ n → selfω n ev p)) (Tω-via-labels ev p) (proj₁ L)) (proj₂ L)
  where L = Tω-label ev p
```

## §5 跨世界的有限测试

**有限测试, 不是证明.** 主线的证书与克隆的证书, 计值在第 0 项上 FGH 相等, `refl`. 只比较这几个点.

```agda
import OCF.Free.Level as FL
import OCF.Free.Force as FF
import OCF.Align.LadderNFMain as FM
import OCF.Align.LadderNFWMain as WM

fgh-Ω·2 : FL.FGH (FF.forceᴺ _ FM.GᴺTΩ·2) 0 ≡ FGH (forceᴺ _ WM.GᴺTΩ·2) 0
fgh-Ω·2 = refl

fgh-Ω·3 : FL.FGH (FF.forceᴺ _ FM.GᴺTΩ·3) 0 ≡ FGH (forceᴺ _ WM.GᴺTΩ·3) 0
fgh-Ω·3 = refl

fgh-Ω·2-val : FL.FGH (FF.forceᴺ _ FM.GᴺTΩ·2) 0 ≡ 1
fgh-Ω·2-val = refl
```

