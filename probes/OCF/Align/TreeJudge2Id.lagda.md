# 恒等读法的 $\psi_0(\Omega_{\Omega+1})$ 没有证书 (否定, 无条件)

> 不含记号 (导入闭包干净). 结论写在 [TreeJudge2](TreeJudge2.lagda.md). 底座 [TreeJudge2Base](TreeJudge2Base.lagda.md), [TreeJudge2Rel](TreeJudge2Rel.lagda.md).
>
> **`no-id : Goodᴺ (T₀ L₁ (wf₁ , sfL) tcI) → ⊥`.** $L_1=\Omega+1$, `tcI` = `Tc-id c₁`. 这是有限测试 `hf-t2id`, `hf-t21id` ([TreeJudgeCheckBad](TreeJudgeCheckBad.lagda.md)) 的定理形式, 目标取最小的: 恒等读法在 $\Omega$ 上不报, 在 $\Omega+1$ 就报 (`b-id`, [TreeJudge2Test](TreeJudge2Test.lagda.md)).
>
> **证明的形状.** $X$ = 根的第 1 项, 闭包, 界 1, 头 $t_0=\psi_0(\psi_\Omega(\Omega_1))$. $\tau=\mathrm{lv}(t_0)$ 是第 0 个链点.
>
> 1. $t_0$ 是极限, 第 0 项是极限, 再第 0 项是 1. 所以证书逼出 $\tau=\lim f$, $f\,0=\lim f_0$, $f_0\,0=1$ (`shape`).
> 2. 分支 $\tau$ 里走第 0 项, 第 0 项, 到节点 $\lceil1\rceil$, 位置 `suc (bra τ e Y)` (`step-lim`, `A₀`, `A₁`).
> 3. 节点的第 1 个链点把闭包 $\Omega_\Omega$ 放到目标 `suc (bra τ e …)` 之下: 恒等读法没有把目标挪出分支 $\tau$, 所以它落成 `oŝ c₀`, $c_0\succ$ `pr τ` $=\tau$ (`gtτ`, 用 [GuardTightBound](GuardTightBound.lagda.md) 的 `cOf-lb₂`). 走这个链点的第 1 项, 第 1 项, 得到闭包的证书, 头律给 $c_0\sqsubseteq\mathrm{lv}(z)$ (`Rest`).
> 4. 头 $z$ 不读 $\tau$: $z\cong^{\mathsf z}$ `Ref` (`head-≅⁻`). $t_0$ 的第一路径上也有 `y` $\cong^{\mathsf z}$ `Ref` (`Hd`). 所以 $\tau+1\sqsubseteq c_0\sqsubseteq\mathrm{lv}(z)\cong\mathrm{lv}(y)\sqsubseteq\tau$ (`pin`, `pinch`).
>
> **为什么不能直接用 `ghost`:** 见 [TreeJudge2Base](TreeJudge2Base.lagda.md). **为什么位置是抽象的:** $f\,0$ 是证书给的函数在 0 处的值, `Cp _ (lim F)` 的类型依赖 $F$, 不能对 $f\,0$ 分情形, 也没有函数外延把 $f$ 换成字面的. 办法: 层号写成变量 $a$ 与等式 $a\equiv\lim f_0$, 位置 $Y:\mathrm{Cp}\,\lceil a\rceil\,\lceil\tau\rceil$ 全称量化, `refl` 之后层号是字面的, 位置是变量; 规范化用 `nfC-id` 这条引理代替计算. 这是这个证明比上一轮估计 (约 300 行) 长的原因, 它约 900 行.
>
> **如实.** 这个定理否定的是**这棵树**, 不是 "恒等读法" 的想法之外的东西. 第 3 步是唯一读恒等读法的地方: 紧的读法把层 0 的目标放进第一支, `bd-bra` 不适用, 界是 1 ([TreeJudge2Hf](TreeJudge2Hf.lagda.md) 的 `hf-class`, 对照 `b-t`). **没有证明 $t_0$ 自己有证书:** 证明从 $G_0$ 只取形状与不等式. 如果 $t_0$ 也没有证书, `no-id` 仍然成立, 但多一个理由 (判断: $t_0$ 有证书, 没有证).
>
> 模块参数 (`Walk`, `Rest`, `Hd`, `Xn`, `Xp`, `Xm`) 都由这棵树实例化, 不是假设.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudge2Id where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Free.Level using (Ordᴵ; _<ᴵ_; _⊑ᴵ_; _≅ᴵ_; _≺ᴵ_; via; z≅; s≅; l≅; s⊑; ⊑ᴵ-trans; ≅ᴵ-sym; ≅ᴵ-trans; toLevel; toLevel-≅; toLevel-⊑; HS; hs; hz; hl; _⊑⁰_; ⊑-trans; ≅-sym)
import OCF.Free.Level as FL
open import OCF.Free.Prefix using (Z; _≅ᶻ_; ≅ᶻ-sym; ≅ᶻ-trans)
open import OCF.Free.Force using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS)
open import OCF.Align.GuardTightLv
open Lv Dom₀
open import OCF.Align.GuardTightTab Dom₀ using (Strict; st-suc; st-lim; st-fst; st-bra; stCp; st⊙; _⊙_)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree
open import OCF.Align.GuardTightCertRel using (⌜_⌝; Emp; FrL; FrG; out-intoU; cv-into)
open import OCF.Align.GuardTightCert using (c₁; wf₁; sf₁)
open import OCF.Align.TreeJudge2Rel using (L₁; tcI; sfL; Ref; head-≅; head-≅⁻; t-c; rel-t; Tgt; tg0; tgp)
open import OCF.Align.TreeJudge2Base using (Pinch; pinch)
open import OCF.Align.TreeJudgeBase using (head-law; lv; lv-≅; ≅ᴵ→⊑; suc⊑self; fp-good; FP; here; ↓l; ↓f)
```

## §1 恒等读法的规范化是恒等

```agda
nfC-id : ∀ L {k} (P : Cp k L) → Σ _ λ t → Σ _ λ r → nfC L (Tc-id L) P ≡ nfc (inj₂ refl) P t r
nfC-id L self = _ , _ , refl
nfC-id (suc b) (suc P) with nfC b (Tc-id b) P | nfC-id b P
... | _ | t , r , refl = _ , _ , refl
nfC-id (lim f) (lim n P) with nfC (f n) (Tc-id (f n)) P | nfC-id (f n) P
... | _ | t , r , refl = _ , _ , refl
nfC-id (lc c t g) (fst P) with nfC t (Tc-id t) P | nfC-id t P
... | _ | t′ , r , refl = _ , _ , refl
nfC-id (lc c t g) (bra η e P) with nfC (g η e) (Tc-id (g η e)) P | nfC-id (g η e) P
... | _ | t′ , r , refl = _ , _ , refl

nfS-id : ∀ L {k} (R : Strict k L) → Σ _ λ t → Σ _ λ r → nfS L (Tc-id L) R ≡ nfs (inj₂ refl) R t r
nfS-id (suc b) (st-suc P) with nfC b (Tc-id b) P | nfC-id b P
... | _ | t , r , refl = _ , _ , refl
nfS-id (lim f) (st-lim n P) with nfC (f n) (Tc-id (f n)) P | nfC-id (f n) P
... | _ | t , r , refl = _ , _ , refl
nfS-id (lc c t g) (st-fst P) with nfC t (Tc-id t) P | nfC-id t P
... | _ | t′ , r , refl = _ , _ , refl
nfS-id (lc c t g) (st-bra η e P) with nfC (g η e) (Tc-id (g η e)) P | nfC-id (g η e) P
... | _ | t′ , r , refl = _ , _ , refl

-- 目标
nfT-id : ∀ {k} (r : k < L₁) → Σ _ λ tb → nfT L₁ tcI r ≡ nft (inj₂ refl) (fromCpS (toCpS r)) tb
nfT-id r with nfC L₁ tcI (toCpS r) | nfC-id L₁ (toCpS r)
... | _ | t , q , refl = _ , refl

open Emb L₁ tcI

-- `ι` 读到记号. `cv` 在定义里是 where 里的函数, 句法上依赖 z, x, 所以存在量词放在它们后面
ι-omk : ∀ {a π ξ k} (Q : Cp a L₁) (R : Strict k a) (lk : Wk ξ π) (ad : AdmC (cov π) (stCp R)) (z : Vs a R ξ) (x : O a π) →
        Σ (Cov (ξ ∪ pF (stCp (st⊙ Q R))) (π ∪ pF Q)) λ cv → Σ (AdmC (cov (ξ ∪ pF (stCp (st⊙ Q R)))) (stCp (st⊙ Q R))) λ ad′ →
        ι a Q (inj₂ refl) (omk R lk ad z x) ≡ ocv cv (omk (st⊙ Q R) ml ad′ (intoV (st⊙ Q R) (outV R z)) (ιV a R (stCp (st⊙ Q R)) (inj₂ refl) z))
ι-omk {π = π} Q R lk ad z x with nfS L₁ tcI (st⊙ Q R) | nfS-id L₁ (st⊙ Q R)
... | _ | t , r , refl = _ , _ , refl
```

## §2 状态的不变量

`Jab`: 活帧都留在输出里 (`ψ_Ω` 上, 节点因此不答 `cj`). `Jev`: 活帧都有表里的证据 (`ψ₀` 上, `riseΩ` 因此不答 `o0`). 地板下降都保持.

```agda
open Fold L₁ wf₁ sfL tcI
open import OCF.Align.GuardTightBound using (module Land)
open import OCF.Free.Floor using (inl; inr; ink)
open Land L₁ wf₁ sfL tcI using (cOf-lb₂)

data IsJ {A : Set} : Maybe A → Set where
  isj : ∀ {x} → IsJ (just x)

Jab : ∀ {E ρ π} → St E ρ π → Set
Jab {π = π} st = ∀ {f} (m : Mem π f) → IsJ (abm (st m))

Jev : ∀ {E ρ π} → St E ρ π → Set
Jev {π = π} st = ∀ {f} (m : Mem π f) → IsJ (ev (st m))

low-ev : ∀ {E ρ f f′} (lk : Lk (κ f) (κ f′)) (lt : fη f ⊲ fη f′) (s : Fs E ρ f′) → IsJ (ev s) → IsJ (ev (proj₁ (proj₂ (fsLow {f = f} {f′ = f′} lk lt s))))
low-ev lk lt (fs (just (evd Pf adf lkf (ℓ , b , q))) nothing) isj = isj
low-ev lk lt (fs (just (evd Pf adf lkf (ℓ , b , q))) (just (ab m k))) isj = isj

low-ab : ∀ {E ρ f f′} (lk : Lk (κ f) (κ f′)) (lt : fη f ⊲ fη f′) (s : Fs E ρ f′) → IsJ (abm s) → IsJ (abm (proj₁ (proj₂ (fsLow {f = f} {f′ = f′} lk lt s))))
low-ab lk lt (fs e (just (ab m k))) isj = isj

map-ev : ∀ {E ρ ρ′ f} (w₁ : Wk ρ ρ′) (s : Fs E ρ f) → IsJ (ev s) → IsJ (ev (mapFs w₁ s))
map-ev w₁ (fs e nothing) h = h
map-ev w₁ (fs e (just (ab m k))) h = h

map-ab : ∀ {E ρ ρ′ f} (w₁ : Wk ρ ρ′) (s : Fs E ρ f) → IsJ (abm s) → IsJ (abm (mapFs w₁ s))
map-ab w₁ (fs e (just (ab m k))) isj = isj

lower-ev : ∀ {E ρ π} (π′ : Fl) (w : Cov π′ π) (st : St E ρ π) → Jev st → Jev (proj₁ (proj₂ (lowerSt π′ w st)))
lower-ev (tk f) w st J m with w hr
... | f′ , m₁ , lk , lt with fsLow {f = f} {f′ = f′} lk lt (st m₁) | low-ev {f = f} {f′ = f′} lk lt (st m₁) (J m₁)
... | σ , F , c′ | h with m
... | hr = h
lower-ev (a ∪ b) w st J m with lowerSt a (λ m₁ → w (ml m₁)) st | lower-ev a (λ m₁ → w (ml m₁)) st J | lowerSt b (λ m₁ → w (mr m₁)) st | lower-ev b (λ m₁ → w (mr m₁)) st J
lower-ev (a ∪ b) w st J (ml m) | σa , sa , ca | ha | σb , sb , cb | hb = map-ev ml (sa m) (ha m)
lower-ev (a ∪ b) w st J (mr m) | σa , sa , ca | ha | σb , sb , cb | hb = map-ev mr (sb m) (hb m)

lower-ab : ∀ {E ρ π} (π′ : Fl) (w : Cov π′ π) (st : St E ρ π) → Jab st → Jab (proj₁ (proj₂ (lowerSt π′ w st)))
lower-ab (tk f) w st J m with w hr
... | f′ , m₁ , lk , lt with fsLow {f = f} {f′ = f′} lk lt (st m₁) | low-ab {f = f} {f′ = f′} lk lt (st m₁) (J m₁)
... | σ , F , c′ | h with m
... | hr = h
lower-ab (a ∪ b) w st J m with lowerSt a (λ m₁ → w (ml m₁)) st | lower-ab a (λ m₁ → w (ml m₁)) st J | lowerSt b (λ m₁ → w (mr m₁)) st | lower-ab b (λ m₁ → w (mr m₁)) st J
lower-ab (a ∪ b) w st J (ml m) | σa , sa , ca | ha | σb , sb , cb | hb = map-ab ml (sa m) (ha m)
lower-ab (a ∪ b) w st J (mr m) | σa , sa , ca | ha | σb , sb , cb | hb = map-ab mr (sb m) (hb m)

toOut-J : ∀ {E ρ π} (st : St E ρ π) → Jab st → ∀ {a b} (r : a < b) (x : Adm (cov π) r) → Σ _ λ a′ → Vis.toOut st r x ≡ just a′
toOut-J st J zero x = tt , refl
toOut-J st J (suc r) x = toOut-J st J r x
toOut-J st J (lim n r) x = toOut-J st J r x
toOut-J st J (fst r) x = toOut-J st J r x
toOut-J st J (bra η e r) ((c₂ , t₂ , g₂ , e₁ , m , k) , x) with abm (st m) | J m | Vis.toOut st r x | toOut-J st J r x
... | just (ab mem lk) | isj | just a′ | a′ , refl = _ , refl

toTab-J : ∀ {E ρ π} (st : St E ρ π) → Jev st → ∀ {a b} (r : a < b) (x : Adm (cov π) r) → Σ _ λ a′ → Vis.toTab st r x ≡ just a′
toTab-J st J zero x = tt , refl
toTab-J st J (suc r) x = toTab-J st J r x
toTab-J st J (lim n r) x = toTab-J st J r x
toTab-J st J (fst r) x = toTab-J st J r x
toTab-J st J (bra η e r) ((c₂ , t₂ , g₂ , e₁ , m , k) , x) with ev (st m) | J m | Vis.toTab st r x | toTab-J st J r x
... | just d | isj | just a′ | a′ , refl = _ , refl
```

## §3 节点的两个方程

```agda
ψΩ-node : ∀ {E ρ π k} (st : St E ρ π) (r₀ : k < c₁) (cv : Adm (cov π) (suc r₀)) (h : ∀ ξ → Us L₁ (suc r₀) ξ → O L₁ (ξ ∪ π)) → Jab st →
          Σ (Adm (cov ρ) r₀) λ a′ →
          ψ E (tp zero tt) st (oΩ (suc r₀) cv h) ≡ oΩ r₀ a′ (λ ξ y → ψ E (tp zero tt) (stξ ξ st) (h ξ (intoU (suc r₀) (tr⁻O (selfAt sf₁ r₀) (outU r₀ y)))))
ψΩ-node st r₀ cv h J with Vis.toOut st r₀ cv | toOut-J st J r₀ cv
... | just a | a , refl = a , refl

rise-eq : ∀ {E ρ π k} (st : St E ρ π) (r : k < L₁) (cv : Adm (cov π) r) (h : ∀ ξ → Us L₁ r ξ → O L₁ (ξ ∪ π)) → Jev st →
          Σ (Adm (tab E) r) λ a → Σ (Adm (tab E) (fromCpS (toCpS r))) λ aq →
          ψ E t0 st (oΩ r cv h) ≡
          ol (λ n → ψ E t0 (stBody (ξᵗ (trim π st {r} a)) (wkᵗ (trim π st {r} a)) st)
                      (h (ξᵗ (trim π st {r} a)) (intoU r (chainᵒ (Tc-at r tcI)
                         (λ z → ψ E (tp (fromCpS (toCpS r)) aq) (stChain (ξᵗ (trim π st {r} a)) (bkᵗ (trim π st {r} a)) (wkᵗ (trim π st {r} a)) st)
                                   (h (ξᵗ (trim π st {r} a)) (intoU r z))) n))))
rise-eq {E} st r cv h J with Vis.toTab st r cv | toTab-J st J r cv
... | just a | a , refl with nfT L₁ tcI r | nfT-id r
...   | _ | tb , refl = a , tb E a , refl

goC-form : ∀ {t π ρ c₁′ t₁ g₁ c₂ t₂ g₂} (E : Ents) (T : Tg E t) (st : St E ρ π) (P : Cp (lc c₂ t₂ g₂) L₁) (k : Lk (lc c₂ t₂ g₂) (lc c₁′ t₁ g₁)) (ap : AdmC (tab E) P)
           (x : O L₁ π) (g : ∀ η e → O L₁ (π ∪ tk (frm c₁′ t₁ g₁ η e)))
           (SS : Sel.S P E ap (λ F → St F ρ π × (Tg F t × AdmC (tab F) P))) (w : Sel.Sl P E ap (Sel.φ SS)) →
           Σ ((η : Ordᴵ) → cOf w ⊑ᴵ η → O t ρ) λ g′ → goC E T st P k ap x g SS w ≡ oŝ (cOf w) (ψ E T st x) g′
goC-form E T st P k ap x g SS (Sel.emp f) = _ , refl
goC-form E T st P k ap x g SS (Sel.sel ℓ K₀ a q y i dm) = _ , refl

-- 闭包 Ω_Ω 在目标之下: 落成字面的 oŝ
land₁ : ∀ {π ρ} {E : Ents} (q₀ : Lv.zero < c₁) (aq : Adm (tab E) (Lv.suc q₀)) (st : St E ρ π) (cv : AdmC (cov π) (Lv.suc {b = c₁} self)) (x : O L₁ π)
        (g : ∀ η e → O L₁ (π ∪ tk (frm (Ordᴵ.suc Ordᴵ.zero) (Lv.suc Lv.zero) (λ η e → ⌜ η ⌝) η e))) →
        Σ ((η : Ordᴵ) → cOf (Sel.wit (SSc E (tp (Lv.suc q₀) aq) st (Lv.suc self) tt)) ⊑ᴵ η → O Lv.zero ρ) λ g′ →
        ψ E (tp (Lv.suc q₀) aq) st (ocl (Lv.suc self) (inj₂ refl) cv x g) ≡ oŝ (cOf (Sel.wit (SSc E (tp (Lv.suc q₀) aq) st (Lv.suc self) tt))) (ψ E (tp (Lv.suc q₀) aq) st x) g′
land₁ {E = E} q₀ aq st cv x g = goC-form E (tp (Lv.suc q₀) aq) st (Lv.suc self) (inj₂ refl) tt x g (SSc E (tp (Lv.suc q₀) aq) st (Lv.suc self) tt) (Sel.wit (SSc E (tp (Lv.suc q₀) aq) st (Lv.suc self) tt))
```

## §4 走树

`Cfg`: 两层折叠的状态与不变量. `W C x`: $\psi_0(\iota(\psi_\Omega x))$ 读成 `Z`, 这就是 $\Omega_\Omega$ 的分支经过第 1 个链点的形状. **位置 `Q` 是抽象的:** `f 0` 是证书给的, 不能分情形 (没有函数外延), 所以 `Ω̇ ⌜f 0⌝` 的 `ι` 不计算; 把位置量化掉, 层号才能写成字面的.

```agda
gl-at : ∀ {f : ℕ → Z} n → Goodᴺ (Z.lim f) → Goodᴺ (f n)
gl-at n (gl G st) = G n

I₁ : ∀ {π} → O c₁ π → O L₁ (π ∪ tz)
I₁ = ι c₁ (Lv.suc self) (inj₂ refl)

-- `ι` 的 owk 行: 存在量词让检查器解出那个 λ
ι-wk : ∀ {a π π′} (Q : Cp a L₁) (w : Wk π′ π) (t : O a π′) → Σ (Wk (π′ ∪ pF Q) (π ∪ pF Q)) λ w′ → ι a Q (inj₂ refl) (owk w t) ≡ owk w′ (ι a Q (inj₂ refl) t)
ι-wk Q w t = _ , refl

ι-cv : ∀ {a π π′} (Q : Cp a L₁) (w : Cov π′ π) (t : O a π′) → Σ (Cov (π′ ∪ pF Q) (π ∪ pF Q)) λ w′ → ι a Q (inj₂ refl) (ocv w t) ≡ ocv w′ (ι a Q (inj₂ refl) t)
ι-cv Q w t = _ , refl

Ωc : O c₁ tz
Ωc = Ω̇ c₁ (Tc-id c₁)

Ωc-form : Σ (Wk (tz ∪ tz) tz) λ w → Σ (AdmC (cov (tz ∪ tz)) (Lv.suc {b = c₁} self)) λ cv →
          Σ (∀ η (e : Ordᴵ.suc Ordᴵ.zero ⊑ᴵ η) → O L₁ ((tz ∪ tz) ∪ tk (frm (Ordᴵ.suc Ordᴵ.zero) (Lv.suc Lv.zero) (λ η e → ⌜ η ⌝) η e))) λ g →
          I₁ Ωc ≡ ocl (Lv.suc self) (inj₂ refl) cv (I₁ (t-c w)) g
Ωc-form = _ , _ , _ , refl

-- 分支 τ 的第 0 项: 位置与规范化都是字面的
Fr₁ : (η : Ordᴵ) → Ordᴵ.suc Ordᴵ.zero ⊑ᴵ η → Frm
Fr₁ η e = frm (Ordᴵ.suc Ordᴵ.zero) (Lv.suc Lv.zero) (λ η e → ⌜ η ⌝) η e


gcc : ∀ η (e : Ordᴵ.suc Ordᴵ.zero ⊑ᴵ η) → O L₁ ((tz ∪ tz) ∪ tk (Fr₁ η e))
gcc = proj₁ (proj₂ (proj₂ Ωc-form))

record Concl (τ : Ordᴵ) : Set where
  constructor concl
  field
    c₀  : Ordᴵ
    gt  : Ordᴵ.suc τ ⊑ᴵ c₀
    z   : Z
    eqz : z ≅ᶻ Ref
    Gz  : Goodᴺ z
    le  : c₀ ⊑ᴵ lv Gz

module Walk (E₁ E₂ : Ents) where
  record Cfg (π₂ : Fl) : Set where
    constructor cfg
    field
      {ρ₁ ρ₂} : Fl
      st₁ : St E₁ ρ₁ (ρ₂ ∪ tz)
      st₂ : St E₂ ρ₂ π₂
      j₁  : Jev st₁
      j₂  : Jab st₂
  open Cfg public

  T₂ : Tg E₂ c₁
  T₂ = tp zero tt

  W : ∀ {π} → Cfg π → O L₁ π → Z
  W C x = rdZ (ψ E₁ t0 (st₁ C) (I₁ (ψ E₂ T₂ (st₂ C) x)))

  cWk : ∀ {π π′} → Wk π′ π → Cfg π → Cfg π′
  cWk w (cfg s₁ s₂ a b) = cfg s₁ (λ m → s₂ (w m)) a (λ m → b (w m))

  W-cv : ∀ {π π′} (C : Cfg π) (w : Cov π′ π) (x : O L₁ π′) → Σ (Cfg π′) λ C′ → W C (ocv w x) ≡ W C′ x
  W-cv {π′ = π′} (cfg {ρ₂ = ρ₂} s₁ s₂ a b) w x =
    cfg (proj₁ (proj₂ (lowerSt (σ ∪ tz) w′ s₁))) (proj₁ (proj₂ L₂))
        (lower-ev (σ ∪ tz) w′ s₁ a) (lower-ab π′ w s₂ b) , refl
    where
    L₂ = lowerSt π′ w s₂
    σ = proj₁ L₂
    w′ = proj₁ (ι-cv (Lv.suc self) (proj₂ (proj₂ L₂)) (ψ E₂ T₂ (proj₁ (proj₂ L₂)) x))

  -- `Ω̇ (lim f)` 的第 n 项是 owk w (omk …). 这个 w 是定义里的扩展 λ, 只能这样取到
  olk : ∀ {a π} → O a π → ℕ → O a π
  olk (ol F) n = F n
  olk x n = x

  Ω̇-wk : ∀ (f : ℕ → LG) (tc : Tc (Lv.lim f)) n → Σ (Wk (tz ∪ tz) tz) λ w →
         olk (Ω̇ (Lv.lim f) tc) n ≡ owk w (omk (st-lim {f = f} n self) ml tt (Ω̇ (f n) (tc n)) (Emb.ι (Lv.lim f) tc (f n) (Lv.lim n self) (inj₂ refl) (Ω̇ (f n) (tc n))))
  Ω̇-wk f tc n = _ , refl

  -- 极限层: 走一项, 嵌入直接到新位置
  Q⁺ : ∀ {f : ℕ → LG} (Q : Cp (Lv.lim f) L₁) n → Cp (f n) L₁
  Q⁺ Q n = stCp (st⊙ Q (st-lim n self))

  step-lim : ∀ {f s} (Q : Cp ⌜ Ordᴵ.lim f s ⌝ L₁) (C : Cfg (tz ∪ pF Q)) n →
             Goodᴺ (W C (ι _ Q (inj₂ refl) (Ω̇ ⌜ Ordᴵ.lim f s ⌝ (Tc-id _)))) →
             Σ (Cfg (tz ∪ pF (Q⁺ Q n))) λ C′ → Goodᴺ (W C′ (ι _ (Q⁺ Q n) (inj₂ refl) (Ω̇ ⌜ f n ⌝ (Tc-id _))))
  step-lim {f} {s} Q C n G = proj₁ cv₂ , subst Goodᴺ (proj₂ cv₂) G₂
    where
    G₁ = gl-at n G
    R = st-lim {f = λ m → ⌜ f m ⌝} n self
    z = Ω̇ ⌜ f n ⌝ (Tc-id _)
    x = Emb.ι ⌜ Ordᴵ.lim f s ⌝ (Tc-id _) ⌜ f n ⌝ (Lv.lim n self) (inj₂ refl) z
    wk₁ = ι-wk Q (proj₁ (Ω̇-wk (λ m → ⌜ f m ⌝) (Tc-id _) n)) (omk R ml tt z x)
    ιo = ι-omk Q R ml tt z x
    C₁ = cWk (proj₁ wk₁) C
    G₂ : Goodᴺ (W C₁ (ocv (proj₁ ιo) (omk (st⊙ Q R) ml (proj₁ (proj₂ ιo)) (intoV (st⊙ Q R) (outV R z)) (ι _ (Q⁺ Q n) (inj₂ refl) z))))
    G₂ = subst (λ u → Goodᴺ (W C₁ u)) (proj₂ (proj₂ ιo)) G₁
    cv₂ = W-cv C₁ (proj₁ ιo) (omk (st⊙ Q R) ml (proj₁ (proj₂ ιo)) (intoV (st⊙ Q R) (outV R z)) (ι _ (Q⁺ Q n) (inj₂ refl) z))
```

## §5 节点 $\lceil 1\rceil$: 走到闭包

节点的第 1 个链点把闭包 `Ω̇ c₁` 放到目标 (路径穿过分支 $\tau$) 之下, 闭包落成 `oŝ c₀`, $c_0$ 读到目标路径上的 $\tau$. 它的头读不到 $\tau$: 头 $\cong$ `Ref`.

```agda
  -- 后半段: 参数都是变量, 所以检查器不会展开前面的折叠
  W₀ : ∀ {ρ₁ ρ₂ π} (s₁ : St E₁ ρ₁ (ρ₂ ∪ tz)) (s₂ : St E₂ ρ₂ π) → O L₁ π → Z
  W₀ s₁ s₂ x = rdZ (ψ E₁ t0 s₁ (I₁ (ψ E₂ T₂ s₂ x)))

  record Sts (π : Fl) : Set where
    constructor sts
    field
      {r₁ r₂} : Fl
      s₁ : St E₁ r₁ (r₂ ∪ tz)
      s₂ : St E₂ r₂ π

  W₁ : ∀ {π} → Sts π → O L₁ π → Z
  W₁ (sts a b) x = W₀ a b x

  W₁-cv : ∀ {π π′} (C : Sts π) (w : Cov π′ π) (x : O L₁ π′) → Σ (Sts π′) λ C′ → W₁ C (ocv w x) ≡ W₁ C′ x
  W₁-cv {π′ = π′} (sts s₁ s₂) w x = sts (proj₁ (proj₂ (lowerSt (σ ∪ tz) w′ s₁))) (proj₁ (proj₂ L₂)) , refl
    where
    L₂ = lowerSt π′ w s₂
    σ = proj₁ L₂
    w′ = proj₁ (ι-cv (Lv.suc self) (proj₂ (proj₂ L₂)) (ψ E₂ T₂ (proj₁ (proj₂ L₂)) x))

  module Rest {f s ρ₁ ξ ρ₂ π₀} (e : Ordᴵ.suc Ordᴵ.zero ⊑ᴵ Ordᴵ.lim f s) (X : Lv.zero < ⌜ Ordᴵ.lim f s ⌝)
              (aq : Adm (tab E₁) (Lv.suc (bra (Ordᴵ.lim f s) e X) )) (pos : Strict Lv.zero L₁) (d : Lv.zero ≈ Lv.zero)
              (S : St E₂ (ξ ∪ ρ₂) (ξ ∪ (tz ∪ π₀)))
              (stB : St E₁ ρ₁ (ξ ∪ (ρ₂ ∪ tz))) (stC : St E₁ ξ (ξ ∪ (ρ₂ ∪ tz)))
              (cvz : O Lv.zero ξ → Cov (ξ ∪ pF (stCp pos)) ((ξ ∪ tz) ∪ π₀))
              (adz : O Lv.zero ξ → AdmC (cov (ξ ∪ pF (stCp pos))) (stCp pos))
              (zzz : O Lv.zero ξ → Vs L₁ pos ξ)
              (Hv : O Lv.zero ξ → O L₁ (ξ ∪ (ρ₂ ∪ tz)))
              (w₀ : Wk tz ξ)
              (H : ∀ z → Hv z ≡ owk asl (I₁ (ψ E₂ T₂ S (owk asl (ocv (cvz z) (omk pos ml (adz z) (zzz z) (ι Lv.zero (stCp pos) (inj₂ refl) (tr⁻O d z))))))))
              (G₂ : Goodᴺ (rdZ (ψ E₁ t0 stB (Hv (ψ E₁ (tp (Lv.suc (bra (Ordᴵ.lim f s) e X)) aq) stC (Hv (owk w₀ (os o0))))))))
              where
    τ : Ordᴵ
    τ = Ordᴵ.lim f s

    T₃ : Tg E₁ Lv.zero
    T₃ = tp (Lv.suc (bra τ e X)) aq

    z₀ : O Lv.zero ξ
    z₀ = owk w₀ (os o0)

    B : ∀ {σ} → O Lv.zero σ → O L₁ (σ ∪ pF (stCp pos))
    B z = ι Lv.zero (stCp pos) (inj₂ refl) (tr⁻O d z)

    Fz : O Lv.zero ξ → O L₁ (ξ ∪ (ρ₂ ∪ tz))
    Fz z = owk asl (I₁ (ψ E₂ T₂ S (owk asl (ocv (cvz z) (omk pos ml (adz z) (zzz z) (B z))))))

    Ch₁ : O Lv.zero ξ
    Ch₁ = ψ E₁ T₃ stC (Fz z₀)

    G₄ : Goodᴺ (rdZ (ψ E₁ t0 stB (Fz Ch₁)))
    G₄ = subst (λ u → Goodᴺ (rdZ (ψ E₁ t0 stB u))) (H Ch₁) (subst (λ u → Goodᴺ (rdZ (ψ E₁ t0 stB (Hv u)))) (cong (ψ E₁ T₃ stC) (H z₀)) G₂)

    Ech : Σ Fl λ σ → Σ (Cov σ ξ) λ c₃ → Σ (ℕ → O Lv.zero σ) λ Gn → Ch₁ ≡ ocv c₃ (ol Gn)
    Ech = _ , _ , _ , refl

    σ = proj₁ Ech
    c₃ = proj₁ (proj₂ Ech)
    Gn = proj₁ (proj₂ (proj₂ Ech))

    C₀ : Sts ((ξ ∪ tz) ∪ π₀)
    C₀ = sts (λ m → stB (asl m)) (λ m → S (asl m))

    cv₁ = W₁-cv C₀ (cvz Ch₁) (omk pos ml (adz Ch₁) (zzz Ch₁) (B Ch₁))
    C₁ = proj₁ cv₁

    G₅ : Goodᴺ (W₁ C₁ (B Ch₁))
    G₅ = subst Goodᴺ (proj₂ cv₁) G₄

    G₆ : Goodᴺ (W₁ C₁ (B (ocv c₃ (ol Gn))))
    G₆ = subst (λ u → Goodᴺ (W₁ C₁ (B u))) (proj₂ (proj₂ (proj₂ Ech))) G₅

    Xs : O Lv.zero σ
    Xs = ol (λ n → tr⁻O d (Gn n))

    ιcv = ι-cv (stCp pos) c₃ Xs
    cv₂ = W₁-cv C₁ (proj₁ ιcv) (ι Lv.zero (stCp pos) (inj₂ refl) Xs)
    C₂ = proj₁ cv₂

    G₇ : Goodᴺ (W₁ C₂ (ι Lv.zero (stCp pos) (inj₂ refl) Xs))
    G₇ = subst Goodᴺ (proj₂ cv₂) G₆

    G₈ : Goodᴺ (W₁ C₂ (B (Gn 1)))
    G₈ = gl-at 1 G₇

    Gn1 : Σ (St E₁ σ (tz ∪ tz)) λ st₄ → Gn 1 ≡ ψ E₁ T₃ st₄ (I₁ Ωc)
    Gn1 = _ , refl

    st₄ = proj₁ Gn1
    wc = proj₁ Ωc-form
    cvc = proj₁ (proj₂ Ωc-form)
    gc′ = proj₁ (proj₂ (proj₂ Ωc-form))

    Ld = land₁ (bra τ e X) aq st₄ cvc (I₁ (t-c wc)) gc′

    wt = Sel.wit (SSc E₁ T₃ st₄ (Lv.suc self) tt)
    t′ = ψ E₁ T₃ st₄ (I₁ (t-c wc))

    G₉ : Goodᴺ (W₁ C₂ (B (oŝ (cOf wt) t′ (proj₁ Ld))))
    G₉ = subst (λ u → Goodᴺ (W₁ C₂ (B u))) (trans (proj₂ Gn1) (proj₂ Ld)) G₈

    HL = head-law G₉

    gtτ : Ordᴵ.suc τ ⊑ᴵ cOf wt
    gtτ with cOf-lb₂ wt (inr (inl (inl ink))) refl
    ... | via d′ r = s⊑ d′ r

    out : Concl τ
    out = concl (cOf wt) gtτ (rdZ (tr⁻O d t′))
                (head-≅⁻ E₁ T₃ (tgp Lv.z≈) st₄ (λ { (ml ()) ; (mr ()) }) d (rel-t wc))
                (proj₁ HL) (proj₂ HL)

  L1 : LG
  L1 = Lv.suc Lv.zero

  module Nd {f s} (e : Ordᴵ.suc Ordᴵ.zero ⊑ᴵ Ordᴵ.lim f s) (Y : Cp L1 ⌜ Ordᴵ.lim f s ⌝) where
    τ : Ordᴵ
    τ = Ordᴵ.lim f s

    Q : Cp L1 L₁
    Q = Lv.suc (bra τ e Y)

    r₀ : Lv.zero < c₁
    r₀ = bra τ e (Y ◁ Lv.zero)

    d : Lv.zero ≈ Lv.zero
    d = selfAt sf₁ r₀

    Q₃ : Cp Lv.zero L₁
    Q₃ = stCp (st⊙ Q (st-suc self))

    Rn : Strict Lv.zero L1
    Rn = st-suc self

    inn : ∀ {ξ} → O Lv.zero ξ → O L1 (ξ ∪ tz)
    inn z = Emb.ι L1 (Tc-id L1) Lv.zero (Lv.suc self) (inj₂ refl) z

    vf : Σ (Adm (cov (tz ∪ pF Q)) (Lv.suc r₀)) λ cv → Σ (∀ ξ → Us L₁ (Lv.suc r₀) ξ → O L₁ (ξ ∪ (tz ∪ pF Q))) λ h′ →
         ι L1 Q (inj₂ refl) (Ω̇ L1 (Tc-id L1)) ≡ oΩ (Lv.suc r₀) cv h′
    vf = _ , _ , refl

    i1f : ∀ {ρ₂} (a′ : Adm (cov ρ₂) r₀) (h″ : ∀ ξ → Us c₁ r₀ ξ → O c₁ (ξ ∪ ρ₂)) →
          Σ (Adm (cov (ρ₂ ∪ tz)) (Lv.suc r₀)) λ ad₃ → Σ (∀ ξ → Us L₁ (Lv.suc r₀) ξ → O L₁ (ξ ∪ (ρ₂ ∪ tz))) λ h‴ →
          ι c₁ (Lv.suc self) (inj₂ refl) (oΩ r₀ a′ h″) ≡ oΩ (Lv.suc r₀) ad₃ h‴
    i1f a′ h″ = _ , _ , refl

    h′ = proj₁ (proj₂ vf)

    module N (C : Cfg (tz ∪ pF Q)) (G : Goodᴺ (W C (ι L1 Q (inj₂ refl) (Ω̇ L1 (Tc-id L1))))) where
      E2 = ψΩ-node (st₂ C) r₀ (proj₁ vf) h′ (j₂ C)
      a′ = proj₁ E2
      h″ : ∀ ξ → Us c₁ r₀ ξ → O c₁ (ξ ∪ ρ₂ C)
      h″ ξ y = ψ E₂ T₂ (stξ ξ (st₂ C)) (h′ ξ (intoU (Lv.suc r₀) (tr⁻O d (outU r₀ y))))

      G₁ : Goodᴺ (rdZ (ψ E₁ t0 (st₁ C) (I₁ (oΩ r₀ a′ h″))))
      G₁ = subst (λ u → Goodᴺ (rdZ (ψ E₁ t0 (st₁ C) (I₁ u)))) (proj₂ E2) G

      ad₃ = proj₁ (i1f a′ h″)
      h‴ = proj₁ (proj₂ (i1f a′ h″))

      Rr = rise-eq (st₁ C) (Lv.suc r₀) ad₃ h‴ (j₁ C)
      a = proj₁ Rr
      aq = proj₁ (proj₂ Rr)
      Tm = trim (ρ₂ C ∪ tz) (st₁ C) {Lv.suc r₀} a
      ξ = ξᵗ Tm
      stB = stBody ξ (wkᵗ Tm) (st₁ C)
      stC = stChain ξ (bkᵗ Tm) (wkᵗ Tm) (st₁ C)
      r′ : Lv.zero < L₁
      r′ = fromCpS (toCpS (Lv.suc r₀))
      T₃ : Tg E₁ Lv.zero
      T₃ = tp r′ aq

      Hv : O Lv.zero ξ → O L₁ (ξ ∪ (ρ₂ C ∪ tz))
      Hv z = h‴ ξ (intoU (Lv.suc r₀) z)

      chain : ℕ → O Lv.zero ξ
      chain = chainᵒ (Tc-at (Lv.suc r₀) tcI) (λ z → ψ E₁ T₃ stC (Hv z))

      G₂ : Goodᴺ (rdZ (ψ E₁ t0 stB (Hv (chain 1))))
      G₂ = gl-at 1 (subst (λ u → Goodᴺ (rdZ u)) (proj₂ (proj₂ Rr)) G₁)

      S = stξ ξ (st₂ C)

      F₀ F₂ : O Lv.zero ξ → O L₁ (ξ ∪ (ρ₂ C ∪ tz))
      F₀ u = owk asl (I₁ (h″ ξ (intoU r₀ u)))
      F₂ u = owk asl (I₁ (ψ E₂ T₂ S (h′ ξ (intoU (Lv.suc r₀) (tr⁻O d u)))))

      F₄ : O L₁ ((ξ ∪ tz) ∪ pF Q) → O L₁ (ξ ∪ (ρ₂ C ∪ tz))
      F₄ u = owk asl (I₁ (ψ E₂ T₂ S (owk asl u)))

      F₃ : O Lv.zero ξ → O L₁ (ξ ∪ (ρ₂ C ∪ tz))
      F₃ u = F₄ (ι L1 Q (inj₂ refl) (omk Rn ml tt u (inn u)))

      ιo : (z′ : O Lv.zero ξ) → _
      ιo z′ = ι-omk Q Rn ml tt z′ (inn z′)

      B : (z : O Lv.zero ξ) → O L₁ (ξ ∪ pF Q₃)
      B z = ι Lv.zero Q₃ (inj₂ refl) (tr⁻O d z)

      Hv-eq : ∀ z → Hv z ≡ F₄ (ocv (proj₁ (ιo (tr⁻O d z))) (omk (st⊙ Q Rn) ml (proj₁ (proj₂ (ιo (tr⁻O d z)))) (intoV (st⊙ Q Rn) (tr⁻O d z)) (B z)))
      Hv-eq z = trans (cong F₀ (out-intoU r₀ z))
                (trans (cong F₂ (out-intoU r₀ z))
                (trans (cong F₃ (cv-into Q Lv.zero (tr⁻O d z)))
                       (cong F₄ (proj₂ (proj₂ (ιo (tr⁻O d z)))))))

      ch1 : ∀ {k π} (tk′ : Tc k) (F : O k π → O k π) → chainᵒ tk′ F 1 ≡ F (chainᵒ tk′ F 0)
      ch1 tk′ F = refl

      ch0 : Σ (Wk tz ξ) λ w₀ → chain 0 ≡ owk w₀ (os o0)
      ch0 = _ , refl

      w₀ = proj₁ ch0

      G₂′ : Goodᴺ (rdZ (ψ E₁ t0 stB (Hv (ψ E₁ T₃ stC (Hv (owk w₀ (os o0)))))))
      G₂′ = subst (λ u → Goodᴺ (rdZ (ψ E₁ t0 stB (Hv u))))
                  (trans (ch1 (Tc-at (Lv.suc r₀) tcI) (λ z → ψ E₁ T₃ stC (Hv z))) (cong (λ z → ψ E₁ T₃ stC (Hv z)) (proj₂ ch0))) G₂

      out : Concl τ
      out = Rest.out e (fromCpS (toCpS (Y ◁ Lv.zero))) aq (st⊙ Q Rn) d S stB stC
                     (λ z → proj₁ (ιo (tr⁻O d z))) (λ z → proj₁ (proj₂ (ιo (tr⁻O d z)))) (λ z → intoV (st⊙ Q Rn) (tr⁻O d z))
                     Hv w₀ Hv-eq G₂′
```

## §6 分支的头两步

`A₁`: 层号是字面的 1, 位置任意. `A₀`: 层号是字面的极限, 第 0 项是 1. 这里的 `a ≡ …` 是证书逼出来的 (`view`), 层号写成变量 $a$, 再用 `refl`, 这样 `f 0` 不必分情形.

```agda
  A₁ : ∀ {f s} (e : Ordᴵ.suc Ordᴵ.zero ⊑ᴵ Ordᴵ.lim f s) (a : Ordᴵ) → a ≡ Ordᴵ.suc Ordᴵ.zero → (Y : Cp ⌜ a ⌝ ⌜ Ordᴵ.lim f s ⌝) →
       (C : Cfg (tz ∪ pF (Lv.suc (bra (Ordᴵ.lim f s) e Y)))) →
       Goodᴺ (W C (ι ⌜ a ⌝ (Lv.suc (bra (Ordᴵ.lim f s) e Y)) (inj₂ refl) (Ω̇ ⌜ a ⌝ (Tc-id _)))) → Concl (Ordᴵ.lim f s)
  A₁ e .(Ordᴵ.suc Ordᴵ.zero) refl Y C G = Nd.N.out e Y C G

  A₀ : ∀ {f s} (e : Ordᴵ.suc Ordᴵ.zero ⊑ᴵ Ordᴵ.lim f s) (a : Ordᴵ) (f₀ : ℕ → Ordᴵ) {s₀} → a ≡ Ordᴵ.lim f₀ s₀ → f₀ 0 ≡ Ordᴵ.suc Ordᴵ.zero → (Y : Cp ⌜ a ⌝ ⌜ Ordᴵ.lim f s ⌝) →
       (C : Cfg (tz ∪ pF (Lv.suc (bra (Ordᴵ.lim f s) e Y)))) →
       Goodᴺ (W C (ι ⌜ a ⌝ (Lv.suc (bra (Ordᴵ.lim f s) e Y)) (inj₂ refl) (Ω̇ ⌜ a ⌝ (Tc-id _)))) → Concl (Ordᴵ.lim f s)
  A₀ {f} {s} e .(Ordᴵ.lim f₀ s₀) f₀ {s₀} refl eq₁ Y C G =
    A₁ e (f₀ 0) eq₁ (Y ⊙ Lv.lim 0 self) (proj₁ Sp) (proj₂ Sp)
    where
    Sp = step-lim (Lv.suc (bra (Ordᴵ.lim f s) e Y)) C 0 G

  module Tp {f s} (e₁ : Ordᴵ.suc Ordᴵ.zero ⊑ᴵ Ordᴵ.lim f s) where
    τ : Ordᴵ
    τ = Ordᴵ.lim f s

    Tτ : O c₁ (tz ∪ (tk (Fr₁ τ e₁) ∪ tz))
    Tτ = Emb.ι c₁ (Tc-id c₁) ⌜ τ ⌝ (bra τ e₁ self) (inj₂ refl) (Ω̇ ⌜ τ ⌝ (Tc-id ⌜ τ ⌝))

    Q₀ : Cp ⌜ f 0 ⌝ L₁
    Q₀ = Lv.suc (bra τ e₁ (Lv.lim 0 self))

    z₀ : O ⌜ f 0 ⌝ tz
    z₀ = Ω̇ ⌜ f 0 ⌝ (Tc-id _)

    Top : Σ Fl λ π₁ → Σ (Wk π₁ ((tz ∪ (tk (Fr₁ τ e₁) ∪ tz)) ∪ tz)) λ w₁ → Σ Fl λ π₂ → Σ (Cov π₂ π₁) λ c₁′ → Σ (Cov (tz ∪ pF Q₀) π₂) λ c₂ →
          Σ (Strict ⌜ f 0 ⌝ L₁) λ pos → Σ (AdmC (cov (tz ∪ pF Q₀)) (stCp pos)) λ ad → Σ (Vs L₁ pos tz) λ zz →
          olk (I₁ Tτ) 0 ≡ owk w₁ (ocv c₁′ (ocv c₂ (omk pos ml ad zz (ι ⌜ f 0 ⌝ Q₀ (inj₂ refl) z₀))))
    Top = _ , _ , _ , _ , _ , _ , _ , _ , refl

    top-step : (C : Cfg ((tz ∪ (tk (Fr₁ τ e₁) ∪ tz)) ∪ tz)) → Goodᴺ (W C (I₁ Tτ)) → Σ (Cfg (tz ∪ pF Q₀)) λ C′ → Goodᴺ (W C′ (ι ⌜ f 0 ⌝ Q₀ (inj₂ refl) z₀))
    top-step C G = proj₁ Cv₂ , subst Goodᴺ (proj₂ Cv₂) (subst Goodᴺ (proj₂ Cv₁) G₀)
      where
      w₁ = proj₁ (proj₂ Top)
      c₁′ = proj₁ (proj₂ (proj₂ (proj₂ Top)))
      c₂ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ Top))))
      pos = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ Top)))))
      ad = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ Top))))))
      zz = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ Top)))))))
      tail = omk pos ml ad zz (ι ⌜ f 0 ⌝ Q₀ (inj₂ refl) z₀)
      G₀ : Goodᴺ (W (cWk w₁ C) (ocv c₁′ (ocv c₂ tail)))
      G₀ = gl-at 0 G
      Cv₁ = W-cv (cWk w₁ C) c₁′ (ocv c₂ tail)
      Cv₂ = W-cv (proj₁ Cv₁) c₂ tail

    branch : ∀ (f₀ : ℕ → Ordᴵ) {s₀} → f 0 ≡ Ordᴵ.lim f₀ s₀ → f₀ 0 ≡ Ordᴵ.suc Ordᴵ.zero → (C : Cfg ((tz ∪ (tk (Fr₁ τ e₁) ∪ tz)) ∪ tz)) → Goodᴺ (W C (I₁ Tτ)) → Concl τ
    branch f₀ eq eq₁ C G = A₀ e₁ (f 0) f₀ eq eq₁ (Lv.lim 0 self) (proj₁ Sp) (proj₂ Sp)
      where
      Sp = top-step C G

    gF : Σ Fl λ π₁ → Σ (Wk π₁ ((tz ∪ tz) ∪ tk (Fr₁ τ e₁))) λ w₃ → Σ (Wk ((tz ∪ (tk (Fr₁ τ e₁) ∪ tz)) ∪ tz) π₁) λ w₄ → gcc τ e₁ ≡ owk w₃ (owk w₄ (I₁ Tτ))
    gF = _ , _ , _ , refl

    concl-of : ∀ (f₀ : ℕ → Ordᴵ) {s₀} → f 0 ≡ Ordᴵ.lim f₀ s₀ → f₀ 0 ≡ Ordᴵ.suc Ordᴵ.zero → (C : Cfg ((tz ∪ tz) ∪ tk (Fr₁ τ e₁))) → Goodᴺ (W C (gcc τ e₁)) → Concl τ
    concl-of f₀ eq eq₁ C G = branch f₀ eq eq₁ (cWk w₄ (cWk w₃ C)) (subst (λ u → Goodᴺ (W C u)) (proj₂ (proj₂ (proj₂ gF))) G)
      where
      w₃ = proj₁ (proj₂ gF)
      w₄ = proj₁ (proj₂ (proj₂ gF))

  brH : ∀ (L : Ordᴵ) (shape : ∀ τ → τ ≅ᴵ L → Σ (ℕ → Ordᴵ) λ f → Σ (∀ n → f n ⊑ᴵ f (suc n)) λ s → (τ ≡ Ordᴵ.lim f s) ×
                       Σ (ℕ → Ordᴵ) λ f₀ → Σ (∀ n → f₀ n ⊑ᴵ f₀ (suc n)) λ s₀ → (f 0 ≡ Ordᴵ.lim f₀ s₀) × (f₀ 0 ≡ Ordᴵ.suc Ordᴵ.zero))
        η (e₁ : Ordᴵ.suc Ordᴵ.zero ⊑ᴵ η) (C : Cfg ((tz ∪ tz) ∪ tk (Fr₁ η e₁))) → η ≅ᴵ L → Goodᴺ (W C (gcc η e₁)) → Concl η
  brH L shape η e₁ C η≅ Gc with shape η η≅
  ... | f , s , refl , f₀ , s₀ , ef , ef₀ = Tp.concl-of e₁ f₀ ef ef₀ C Gc

  cast₁ : ∀ {ρ₁ ρ₂ π f} (s₁ : St E₁ ρ₁ ((ρ₂ ∪ tz) ∪ tk f)) (s₂ : St E₂ (ρ₂ ∪ tk f) π) (j₁ : Jev (λ {f₁} (m : Mem ((ρ₂ ∪ tk f) ∪ tz) f₁) → s₁ (sw₃ m))) (j₂ : Jab s₂) (x : O L₁ π) →
          rdZ (ψ E₁ t0 s₁ (owk sw₃ (I₁ (ψ E₂ T₂ s₂ x)))) ≡ W (cfg (λ m → s₁ (sw₃ m)) s₂ j₁ j₂) x
  cast₁ s₁ s₂ j₁ j₂ x = refl
```

## §7 第 1 个链点的形状

`keep-form`: 目标是 $\Omega$ 本身: 闭包保留. `X-form`: 目标 0, 上下文空: 闭包计值, 界是 1. 这两条对抽象的 `x`, `g` 写, 所以 `refl` 解得出定义里的状态.

```agda
keep-form : ∀ {E ρ π} (st : St E ρ π) (cv : AdmC (cov π) (Lv.suc {b = c₁} self)) (x : O L₁ π) (g : ∀ η e → O L₁ (π ∪ tk (Fr₁ η e))) →
            Σ (AdmC (cov ρ) (self {c₁})) λ a → Σ (∀ {η} → Ordᴵ.suc Ordᴵ.zero ⊑ᴵ η → Ordᴵ.suc Ordᴵ.zero ⊑ᴵ η) λ eg → Σ (∀ η e′ → St E (ρ ∪ tk (Fr₁ η e′)) (π ∪ tk (Fr₁ η (eg e′)))) λ s′ →
            (ψ E (tp zero tt) st (ocl (Lv.suc self) (inj₂ refl) cv x g) ≡ ocl self (inj₂ refl) a (ψ E (tp zero tt) st x) (λ η e′ → ψ E (tp zero tt) (s′ η e′) (g η (eg e′)))) ×
            (Jab st → ∀ η e′ → Jab (s′ η e′))
keep-form st cv x g = _ , _ , _ , refl , (λ j η e′ → λ { (ml m) → map-ab ml (st m) (j m) ; (mr hr) → isj })

X-form : ∀ {E ρ} (st : St E ρ (tz ∪ tz)) (cv : AdmC (cov (tz ∪ tz)) (Lv.suc {b = c₁} self)) (x : O L₁ (tz ∪ tz)) (g : ∀ η e → O L₁ ((tz ∪ tz) ∪ tk (Fr₁ η e))) →
         Σ (∀ {η} → Ordᴵ.suc Ordᴵ.zero ⊑ᴵ η → Ordᴵ.suc Ordᴵ.zero ⊑ᴵ η) λ ge → Σ (∀ η d → St (E ▸ c₁ , Ordᴵ.suc η) ρ ((tz ∪ tz) ∪ tk (Fr₁ η (ge d)))) λ s₁ →
         (ψ E t0 st (ocl (Lv.suc self) (inj₂ refl) cv x g) ≡ oŝ (Ordᴵ.suc Ordᴵ.zero) (ψ E t0 st x) (λ η d → ψ (E ▸ c₁ , Ordᴵ.suc η) t0 (s₁ η d) (g η (ge d)))) ×
         (∀ η d → Jev (s₁ η d))
X-form st cv x g = _ , _ , refl , (λ η d → λ { (ml (ml ())) ; (ml (mr ())) ; (mr hr) → isj })

lvLim : ∀ {h : ℕ → Z} (G : Goodᴺ (Z.lim h)) τ → τ ≅ᴵ lv G → Σ (ℕ → Ordᴵ) λ f → Σ (∀ n → f n ⊑ᴵ f (suc n)) λ s → (τ ≡ Ordᴵ.lim f s) × Σ (Goodᴺ (h 0)) λ G′ → f 0 ≅ᴵ lv G′
lvLim (gl G st) .(Ordᴵ.lim _ _) (l≅ k) = _ , _ , refl , G 0 , k 0

lv1 : (G : Goodᴺ (Z.suc Z.zero)) (a : Ordᴵ) → a ≅ᴵ lv G → a ≡ Ordᴵ.suc Ordᴵ.zero
lv1 (gs gz) .(Ordᴵ.suc Ordᴵ.zero) (s≅ z≅) = refl
```

## §7′ 头那一边

`Hd`: 头 $\psi_0(\psi_\Omega(\Omega_1))$. 状态都是变量, 第一路径都是字面的.

```agda
sub⊑ : ∀ {a b} (e : a ≡ b) (H : Goodᴺ a) → forceᴺ b (subst Goodᴺ e H) ⊑⁰ forceᴺ a H
sub⊑ refl H h = h

down : ∀ {x} {h : ℕ → Z} (e : x ≡ Z.lim h) (G : Goodᴺ x) n → Σ (Goodᴺ (h n)) λ G′ → forceᴺ _ G′ ⊑⁰ forceᴺ _ G
down refl G n = fp-good (↓l n here) G

shape₀ : ∀ {x} {h : ℕ → Z} (e : x ≡ Z.lim h) (G : Goodᴺ x) τ → τ ≅ᴵ lv G → Σ (ℕ → Ordᴵ) λ f → Σ (∀ n → f n ⊑ᴵ f (suc n)) λ s → (τ ≡ Ordᴵ.lim f s) × Σ (Goodᴺ (h 0)) λ G′ → f 0 ≅ᴵ lv G′
shape₀ refl G τ τ≅ = lvLim G τ τ≅

lv1′ : ∀ {x} (e : x ≡ Z.suc Z.zero) (G : Goodᴺ x) (a : Ordᴵ) → a ≅ᴵ lv G → a ≡ Ordᴵ.suc Ordᴵ.zero
lv1′ refl G a k = lv1 G a k

module FactsG {tt₀ : Z} {H h : ℕ → Z} {c₀ y o₀} {gz oz : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z}
               (e₁ : tt₀ ≡ Z.lim H) (e₂ : H 0 ≡ Z.lim h) (e₃ : h 0 ≡ Z.suc Z.zero) (e₅ : h 1 ≡ Z.ĉᴸ c₀ y gz o₀ oz) (e₆ : o₀ ≡ y)
               (G₀ : Goodᴺ tt₀) where
  shape : ∀ τ → τ ≅ᴵ lv G₀ → Σ (ℕ → Ordᴵ) λ f → Σ (∀ n → f n ⊑ᴵ f (suc n)) λ s → (τ ≡ Ordᴵ.lim f s) ×
          Σ (ℕ → Ordᴵ) λ f₀ → Σ (∀ n → f₀ n ⊑ᴵ f₀ (suc n)) λ s₀ → (f 0 ≡ Ordᴵ.lim f₀ s₀) × (f₀ 0 ≡ Ordᴵ.suc Ordᴵ.zero)
  shape τ τ≅ with shape₀ e₁ G₀ τ τ≅
  ... | f , s , eτ , G₁₀ , f0≅ with shape₀ e₂ G₁₀ (f 0) f0≅
  ...   | f₀ , s₀ , ef , G₂₀ , f₀0≅ = f , s , eτ , f₀ , s₀ , ef , lv1′ e₃ G₂₀ (f₀ 0) f₀0≅

  D₀ = down e₁ G₀ 0
  D₁ = down e₂ (proj₁ D₀) 1
  Gh = proj₁ D₁
  Fy₀ = fp-good (↓f here) (subst Goodᴺ e₅ Gh)

  Gy : Goodᴺ y
  Gy = subst Goodᴺ e₆ (proj₁ Fy₀)

  y≤ : lv Gy ⊑ᴵ lv G₀
  y≤ = toLevel-⊑ (forceᴺ-HS _ Gy) (forceᴺ-HS _ G₀)
         (⊑-trans (sub⊑ e₆ (proj₁ Fy₀)) (⊑-trans (proj₂ Fy₀) (⊑-trans (sub⊑ e₅ Gh) (⊑-trans (proj₂ D₁) (proj₂ D₀)))))

module Hd (E₀ : Ents) {ρ₁ : Fl} (stB : St E₀ ρ₁ (tz ∪ tz)) (stC : St E₀ tz (tz ∪ tz)) (wc : Wk (tz ∪ tz) tz) where
  open Walk E₀ E₀ using (Sts; sts; W₁; W₁-cv; T₂)
  r₀ : Lv.zero < c₁
  r₀ = fst zero

  x₀ : O L₁ (tz ∪ tz)
  x₀ = I₁ (t-c wc)

  tt₀ : Z
  tt₀ = rdZ (ψ E₀ t0 stB (I₁ (ψ E₀ T₂ stC x₀)))

  πv : Fl
  πv = (tz ∪ tz) ∪ tz

  vf : Σ (Wk πv (tz ∪ tz)) λ w₁ → Σ (Adm (cov πv) (Lv.suc r₀)) λ cv → Σ (∀ ξ → Us L₁ (Lv.suc r₀) ξ → O L₁ (ξ ∪ πv)) λ hh →
       x₀ ≡ owk w₁ (oΩ (Lv.suc r₀) cv hh)
  vf = _ , _ , _ , refl

  hh-form : ∀ ξ (z : O Lv.zero ξ) → Σ Fl λ π₀ → Σ (Wk π₀ (ξ ∪ πv)) λ w₃ → Σ Fl λ π₁ → Σ (Wk π₁ π₀) λ w₄ → Σ Fl λ π₂ → Σ (Cov π₂ π₁) λ c₃ →
            Σ (Strict Lv.zero L₁) λ pos → Σ (Cov (ξ ∪ pF (stCp pos)) π₂) λ c₄ → Σ (AdmC (cov (ξ ∪ pF (stCp pos))) (stCp pos)) λ ad → Σ (Vs L₁ pos ξ) λ zz →
            proj₁ (proj₂ (proj₂ vf)) ξ (intoU (Lv.suc r₀) z) ≡ owk w₃ (owk w₄ (ocv c₃ (ocv c₄ (omk pos ml ad zz (ι Lv.zero (stCp pos) (inj₂ refl) z)))))
  hh-form ξ z = _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , refl

  w₁ = proj₁ vf
  cv₀ = proj₁ (proj₂ vf)
  hh = proj₁ (proj₂ (proj₂ vf))

  st₂′ : St E₀ tz πv
  st₂′ m = stC (w₁ m)

  E2 = ψΩ-node st₂′ r₀ cv₀ hh (λ { (ml (ml ())) ; (ml (mr ())) ; (mr ()) })
  a′ = proj₁ E2
  d : Lv.zero ≈ Lv.zero
  d = selfAt sf₁ r₀

  h″ : ∀ ξ → Us c₁ r₀ ξ → O c₁ (ξ ∪ tz)
  h″ ξ y = ψ E₀ T₂ (stξ ξ st₂′) (hh ξ (intoU (Lv.suc r₀) (tr⁻O d (outU r₀ y))))

  i1f : Σ (Adm (cov (tz ∪ tz)) (Lv.suc r₀)) λ ad₃ → Σ (∀ ξ → Us L₁ (Lv.suc r₀) ξ → O L₁ (ξ ∪ (tz ∪ tz))) λ h‴ → I₁ (oΩ r₀ a′ h″) ≡ oΩ (Lv.suc r₀) ad₃ h‴
  i1f = _ , _ , refl

  ad₃ = proj₁ i1f
  h‴ = proj₁ (proj₂ i1f)

  Rr = rise-eq stB (Lv.suc r₀) ad₃ h‴ (λ { (ml ()) ; (mr ()) })
  a = proj₁ Rr
  Tm = trim (tz ∪ tz) stB {Lv.suc r₀} a
  ξ = ξᵗ Tm
  stBb = stBody ξ (wkᵗ Tm) stB
  stCc = stChain ξ (bkᵗ Tm) (wkᵗ Tm) stB
  T₃ : Tg E₀ Lv.zero
  T₃ = tp (fromCpS (toCpS (Lv.suc r₀))) (proj₁ (proj₂ Rr))

  Hv : O Lv.zero ξ → O L₁ (ξ ∪ (tz ∪ tz))
  Hv z = h‴ ξ (intoU (Lv.suc r₀) z)

  chain : ℕ → O Lv.zero ξ
  chain = chainᵒ (Tc-at (Lv.suc r₀) tcI) (λ z → ψ E₀ T₃ stCc (Hv z))

  H : ℕ → Z
  H n = rdZ (ψ E₀ t0 stBb (Hv (chain n)))

  e₁ : tt₀ ≡ Z.lim H
  e₁ = trans (cong (λ u → rdZ (ψ E₀ t0 stB (I₁ u))) (trans (cong (ψ E₀ T₂ stC) (proj₂ (proj₂ (proj₂ vf)))) (proj₂ E2)))
             (trans (cong (λ u → rdZ (ψ E₀ t0 stB u)) (proj₂ (proj₂ i1f))) (cong rdZ (proj₂ (proj₂ Rr))))

  ch0 : Σ (Wk tz ξ) λ w₀ → chain 0 ≡ owk w₀ (os o0)
  ch0 = _ , refl
  w₀ = proj₁ ch0

  S = stξ ξ st₂′

  z′ : O Lv.zero ξ
  z′ = owk w₀ (os o0)

  Hf = hh-form ξ z′
  w₃ = proj₁ (proj₂ Hf)
  w₄ = proj₁ (proj₂ (proj₂ (proj₂ Hf)))
  c₃ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ Hf)))))
  pos = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ Hf))))))
  c₄ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ Hf)))))))
  ad = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ Hf))))))))
  zz = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ Hf)))))))))
  hEq = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ Hf)))))))))

  b : O L₁ (ξ ∪ pF (stCp pos))
  b = ι Lv.zero (stCp pos) (inj₂ refl) z′

  C₀ : Sts (proj₁ (proj₂ (proj₂ Hf)))
  C₀ = sts (λ m → stBb (asl m)) (λ m → S (w₃ (w₄ m)))

  Cv₁ = W₁-cv C₀ c₃ (ocv c₄ (omk pos ml ad zz b))
  Cv₂ = W₁-cv (proj₁ Cv₁) c₄ (omk pos ml ad zz b)
  C₂ = proj₁ Cv₂

  -- 抽象的状态上, 算 `ψ_Ω 1` 的前两项
  os-form : ∀ {π π₀} (C : Sts π) (w : Wk π₀ π) → Σ (ℕ → Z) λ h → (W₁ C (owk w (os o0)) ≡ Z.lim h) × (h 0 ≡ Z.suc Z.zero) × Σ (St E₀ (Sts.r₁ C) (tz ∪ tz)) λ st′ → h 1 ≡ rdZ (ψ E₀ t0 st′ (I₁ Ωc))
  os-form (sts s₁ s₂) w = _ , refl , refl , _ , refl

  bf : Σ (Wk (tz ∪ pF (stCp pos)) (ξ ∪ pF (stCp pos))) λ w″ → b ≡ owk w″ (os o0)
  bf = _ , refl

  Of = os-form C₂ (proj₁ bf)

  mk : W₁ C₂ (omk pos ml ad zz b) ≡ W₁ C₂ b
  mk = mk′ C₂
    where
    mk′ : ∀ (C : Sts _) → W₁ C (omk pos ml ad zz b) ≡ W₁ C b
    mk′ (sts s₁ s₂) = refl

  e₂ : H 0 ≡ Z.lim (proj₁ Of)
  e₂ = trans (cong (λ u → rdZ (ψ E₀ t0 stBb (owk asl (I₁ (ψ E₀ T₂ S u))))) hEq)
             (trans (proj₂ Cv₁) (trans (proj₂ Cv₂) (trans mk (trans (cong (W₁ C₂) (proj₂ bf)) (proj₁ (proj₂ Of))))))

  e₃ = proj₁ (proj₂ (proj₂ Of))
  st′ = proj₁ (proj₂ (proj₂ (proj₂ Of)))
  e₄ = proj₂ (proj₂ (proj₂ (proj₂ Of)))

  wc′ = proj₁ Ωc-form
  cvc = proj₁ (proj₂ Ωc-form)
  XFy = X-form st′ cvc (I₁ (t-c wc′)) gcc

  y : Z
  y = rdZ (ψ E₀ t0 st′ (I₁ (t-c wc′)))

  oy : (η : Ordᴵ) → Ordᴵ.suc Ordᴵ.zero ⊑ᴵ η → O Lv.zero _
  oy η d = ψ (E₀ ▸ c₁ , Ordᴵ.suc η) t0 (proj₁ (proj₂ XFy) η d) (gcc η (proj₁ XFy d))

  e₅ : proj₁ Of 1 ≡ rdZ (oŝ (Ordᴵ.suc Ordᴵ.zero) (ψ E₀ t0 st′ (I₁ (t-c wc′))) oy)
  e₅ = trans e₄ (trans (cong (λ u → rdZ (ψ E₀ t0 st′ u)) (proj₂ (proj₂ (proj₂ Ωc-form)))) (cong rdZ (proj₁ (proj₂ (proj₂ XFy)))))

  module Facts = FactsG {H = H} e₁ e₂ e₃ e₅ refl

  y≅ : y ≅ᶻ Ref
  y≅ = head-≅ E₀ t0 tg0 st′ (λ { (ml ()) ; (mr ()) }) (rel-t wc′)

```

## §8 否定

```agda
module Xn (E₀ : Ents) {ρ₁ : Fl} (stB : St E₀ ρ₁ (tz ∪ tz)) (stC′ : St E₀ tz (tz ∪ tz)) (wc : Wk (tz ∪ tz) tz)
          (eg : ∀ {η} → Ordᴵ.suc Ordᴵ.zero ⊑ᴵ η → Ordᴵ.suc Ordᴵ.zero ⊑ᴵ η)
          (s′ : ∀ η e′ → St E₀ (tz ∪ tk (Fr₁ η e′)) ((tz ∪ tz) ∪ tk (Fr₁ η (eg e′))))
          (kJ : ∀ η e′ → Jab (s′ η e′))
          (ge : ∀ {η} → Ordᴵ.suc Ordᴵ.zero ⊑ᴵ η → Ordᴵ.suc Ordᴵ.zero ⊑ᴵ η)
          (s₁ : ∀ η d → St (E₀ ▸ c₁ , Ordᴵ.suc η) ρ₁ ((tz ∪ tz) ∪ tk (Fr₁ η (ge d))))
          (xJ : ∀ η d → Jev (s₁ η d)) where
  T₂ : Tg E₀ c₁
  T₂ = tp zero tt

  t₁ : O c₁ tz
  t₁ = ψ E₀ T₂ stC′ (I₁ (t-c wc))

  g₁ : ∀ η e′ → O c₁ (tz ∪ tk (Fr₁ η e′))
  g₁ η e′ = ψ E₀ T₂ (s′ η e′) (gcc η (eg e′))

  g₂ : ∀ η e → O L₁ ((tz ∪ tz) ∪ tk (Fr₁ η e))
  g₂ η e = owk sw₃ (I₁ (g₁ η e))

  x₂ = ψ E₀ t0 stB (I₁ t₁)

  o₂ : (η : Ordᴵ) → Ordᴵ.suc Ordᴵ.zero ⊑ᴵ η → O Lv.zero ρ₁
  o₂ η d = ψ (E₀ ▸ c₁ , Ordᴵ.suc η) t0 (s₁ η d) (g₂ η (ge d))

  open Hd E₀ stB stC′ wc using (tt₀; y; y≅; module Facts)

  pin : Pinch tt₀ (λ η e → rdZ (o₂ η e))
  pin G₀ τ e τ≅ Gb = Concl.c₀ c , Concl.gt c , Concl.z c , Concl.Gz c , Concl.le c ,
                     ⊑ᴵ-trans (≅ᴵ→⊑ (lv-≅ (≅ᶻ-trans (Concl.eqz c) (≅ᶻ-sym y≅)) (Concl.Gz c) (Facts.Gy G₀))) (Facts.y≤ G₀)
    where
    module W′ = Walk (E₀ ▸ c₁ , Ordᴵ.suc τ) E₀
    C : W′.Cfg ((tz ∪ tz) ∪ tk (Fr₁ τ (eg (ge e))))
    C = W′.cfg (λ m → s₁ τ e (sw₃ m)) (s′ τ (ge e)) (λ m → xJ τ e (sw₃ m)) (kJ τ (ge e))
    c : Concl τ
    c = W′.brH (lv G₀) (Facts.shape G₀) τ (eg (ge e)) C τ≅ (subst Goodᴺ (W′.cast₁ (s₁ τ e) (s′ τ (ge e)) (λ m → xJ τ e (sw₃ m)) (kJ τ (ge e)) (gcc τ (eg (ge e)))) Gb)

  fin : Goodᴺ (rdZ (oŝ (Ordᴵ.suc Ordᴵ.zero) x₂ o₂)) → ⊥
  fin = pinch pin

iocl : ∀ {ρ} (a : AdmC (cov ρ) (self {c₁})) (t : O c₁ ρ) (g : ∀ η e′ → O c₁ (ρ ∪ tk (Fr₁ η e′))) →
       Σ (AdmC (cov (ρ ∪ tz)) (Lv.suc {b = c₁} self)) λ cv₂ → I₁ (ocl self (inj₂ refl) a t g) ≡ ocl (Lv.suc self) (inj₂ refl) cv₂ (I₁ t) (λ η e → owk sw₃ (I₁ (g η e)))
iocl a t g = _ , refl

wk-ψ : ∀ {E t π π′ ρ} (T : Tg E t) (st : St E ρ π) (w : Wk π′ π) (x : O L₁ π′) → ψ E T st (owk w x) ≡ ψ E T (λ m → st (w m)) x
wk-ψ T st w x = refl

-- 后半: 保留下来的闭包再被计值, 状态都是变量
module Xp (E₀ : Ents) {ρ₁ : Fl} (stB : St E₀ ρ₁ (tz ∪ tz)) (stC′ : St E₀ tz (tz ∪ tz)) (wc : Wk (tz ∪ tz) tz)
          (a : AdmC (cov tz) (self {c₁}))
          (eg : ∀ {η} → Ordᴵ.suc Ordᴵ.zero ⊑ᴵ η → Ordᴵ.suc Ordᴵ.zero ⊑ᴵ η)
          (s′ : ∀ η e′ → St E₀ (tz ∪ tk (Fr₁ η e′)) ((tz ∪ tz) ∪ tk (Fr₁ η (eg e′))))
          (kJ : ∀ η e′ → Jab (s′ η e′))
          (G₁ : Goodᴺ (rdZ (ψ E₀ t0 stB (I₁ (ocl self (inj₂ refl) a (ψ E₀ (tp zero tt) stC′ (I₁ (t-c wc))) (λ η e′ → ψ E₀ (tp zero tt) (s′ η e′) (gcc η (eg e′))))))))
          where
  T₂ : Tg E₀ c₁
  T₂ = tp zero tt

  t₁ : O c₁ tz
  t₁ = ψ E₀ T₂ stC′ (I₁ (t-c wc))

  g₁ : ∀ η e′ → O c₁ (tz ∪ tk (Fr₁ η e′))
  g₁ η e′ = ψ E₀ T₂ (s′ η e′) (gcc η (eg e′))

  g₂ : ∀ η e → O L₁ ((tz ∪ tz) ∪ tk (Fr₁ η e))
  g₂ η e = owk sw₃ (I₁ (g₁ η e))

  io = iocl a t₁ g₁

  XF = X-form stB (proj₁ io) (I₁ t₁) g₂

  absurd : ⊥
  absurd = Xn.fin E₀ stB stC′ wc eg s′ kJ (proj₁ XF) (proj₁ (proj₂ XF)) (proj₂ (proj₂ (proj₂ XF)))
             (subst (λ u → Goodᴺ (rdZ u)) (proj₁ (proj₂ (proj₂ XF))) (subst (λ u → Goodᴺ (rdZ (ψ E₀ t0 stB u))) (proj₂ io) G₁))

-- 前半: 第 1 个链点, 闭包在目标 Ω 上保留
module Xm (E₀ : Ents) {ρ₁ : Fl} (stB : St E₀ ρ₁ (tz ∪ tz)) (stC : St E₀ tz (tz ∪ tz)) (w₀ : Wk tz tz)
          (G : Goodᴺ (rdZ (ψ E₀ t0 stB (I₁ (ψ E₀ (tp zero tt) stC (I₁ (owk w₀ Ωc))))))) where
  T₂ : Tg E₀ c₁
  T₂ = tp zero tt

  wc = proj₁ Ωc-form
  cvc = proj₁ (proj₂ Ωc-form)

  ιw = ι-wk (Lv.suc self) w₀ Ωc
  w′ = proj₁ ιw

  stC′ : St E₀ tz (tz ∪ tz)
  stC′ m = stC (w′ m)

  KF = keep-form stC′ cvc (I₁ (t-c wc)) gcc

  e-a : ψ E₀ T₂ stC (I₁ (owk w₀ Ωc)) ≡ ocl self (inj₂ refl) (proj₁ KF) (ψ E₀ T₂ stC′ (I₁ (t-c wc))) (λ η e′ → ψ E₀ T₂ (proj₁ (proj₂ (proj₂ KF)) η e′) (gcc η (proj₁ (proj₂ KF) e′)))
  e-a = trans (cong (ψ E₀ T₂ stC) (proj₂ ιw)) (trans (wk-ψ T₂ stC w′ (I₁ Ωc)) (trans (cong (ψ E₀ T₂ stC′) (proj₂ (proj₂ (proj₂ Ωc-form)))) (proj₁ (proj₂ (proj₂ (proj₂ KF))))))

  absurd : ⊥
  absurd = Xp.absurd E₀ stB stC′ wc (proj₁ KF) (proj₁ (proj₂ KF)) (proj₁ (proj₂ (proj₂ KF)))
             (proj₂ (proj₂ (proj₂ (proj₂ KF))) (λ { (ml ()) ; (mr ()) }))
             (subst (λ u → Goodᴺ (rdZ (ψ E₀ t0 stB (I₁ u)))) e-a G)

-- 根: 第 1 项就是 Xm 的形状
E∅ : Ents
E∅ = ∅ Ordᴵ.zero

Tf : Σ (St E∅ tz tz) λ st₀ → T L₁ (wf₁ , sfL) tcI ≡ ψ E∅ t0 st₀ (Ω̇ L₁ tcI)
Tf = _ , refl

Ωs : Σ (∀ ξ → O c₁ ξ → O L₁ (ξ ∪ tz)) λ h₀ → Ω̇ L₁ tcI ≡ oΩ zero tt h₀
Ωs = _ , refl

h₀ = proj₁ Ωs

h₀-ψ : ∀ {t ρ ξ} (T′ : Tg E∅ t) (st : St E∅ ρ (ξ ∪ tz)) (z : O c₁ ξ) → ψ E∅ T′ st (h₀ ξ z) ≡ ψ E∅ T′ st (I₁ z)
h₀-ψ T′ st z = refl

st₀ = proj₁ Tf

Rr₀ = rise-eq st₀ zero tt h₀ (λ ())

Tm₀ = trim tz st₀ {zero} (proj₁ Rr₀)
ξ₀ : Fl
ξ₀ = ξᵗ Tm₀
stB₀ = stBody ξ₀ (wkᵗ Tm₀) st₀
stC₀ = stChain ξ₀ (bkᵗ Tm₀) (wkᵗ Tm₀) st₀

ch-f : O c₁ ξ₀ → O c₁ ξ₀
ch-f z = ψ E∅ (tp zero tt) stC₀ (h₀ ξ₀ z)

ch-1 : ∀ {k π} (tk′ : Tc k) (F : O k π → O k π) → chainᵒ tk′ F 1 ≡ F (chainᵒ tk′ F 0)
ch-1 tk′ F = refl

ch-0 : Σ (Wk tz ξ₀) λ w₀ → chainᵒ (Tc-at zero tcI) ch-f 0 ≡ owk w₀ Ωc
ch-0 = _ , refl

-- 恒等读法的 ψ₀(Ω_{Ω+1}) 没有证书
no-id : Goodᴺ (T₀ L₁ (wf₁ , sfL) tcI) → ⊥
no-id G = Xm.absurd E∅ stB₀ stC₀ (proj₁ ch-0) G₃
  where
  G₁ : Goodᴺ (rdZ (ψ E∅ t0 st₀ (oΩ zero tt h₀)))
  G₁ = G
  G₂ : Goodᴺ (rdZ (ψ E∅ t0 stB₀ (h₀ ξ₀ (chainᵒ (Tc-at zero tcI) ch-f 1))))
  G₂ = gl-at 1 (subst (λ u → Goodᴺ (rdZ u)) (proj₂ (proj₂ Rr₀)) G₁)
  e : chainᵒ (Tc-at zero tcI) ch-f 1 ≡ ψ E∅ (tp zero tt) stC₀ (I₁ (owk (proj₁ ch-0) Ωc))
  e = trans (ch-1 (Tc-at zero tcI) ch-f) (trans (cong ch-f (proj₂ ch-0)) (h₀-ψ (tp zero tt) stC₀ (owk (proj₁ ch-0) Ωc)))
  G₃ : Goodᴺ (rdZ (ψ E∅ t0 stB₀ (I₁ (ψ E∅ (tp zero tt) stC₀ (I₁ (owk (proj₁ ch-0) Ωc))))))
  G₃ = subst Goodᴺ (cong rdZ (h₀-ψ t0 stB₀ _)) (subst (λ u → Goodᴺ (rdZ (ψ E∅ t0 stB₀ (h₀ ξ₀ u)))) e G₂)
```
