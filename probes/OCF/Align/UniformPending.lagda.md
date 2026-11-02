# 无悬置的闭包定理 (二): 阶段塔、增长与判据

> 接 [UniformPendingBase](UniformPendingBase.lagda.md). 任务是检验闭包定理能否跨越帧数 $k$.
>
> 结论先说:
>
> 1. **判据的回答: 部分.** 编译了的部分对 $k$ 一致: 地板 (`pfl-k`)、增长 (`grow-k`, 也对两层上下文 `Nest`)、覆盖的生成 (`PC-base`, `PC-step`, `Link`). 没有编译: 遗传好树与 $k\ge2$ 的证书. 统一折叠上的 $\psi_0(\Omega_\Omega\cdot2)$ 证书与验收**没有做**, $\psi_0(\Omega_\Omega\cdot3)$、$\psi_0(\Omega_\Omega\cdot k)$、$\psi_0(\Omega_\Omega\cdot\omega)$ 也没有.
> 2. **第一处障碍在 $k=3$, 不是纸面上的阶段差 (§6).** Pending 的 `mC` 层允许节点任意高, 只因 $\psi^{[]}$ 不弹栈. $P_2$ 的闭包分支是 $\psi^{P_1}_b(\Omega_\eta)$, $\eta$ 任意高, 它**弹栈**, 弹出的闭包界 $b'+1$ 高于目标 $b$. 这个闭包在 $\psi_0(P_2+\psi_b(\cdot))$ 之下被支配的理由是 $b$ 这一层上下文自己的链, 不是单层 `ColC P₂` (对一切 $P_2$-折叠) 能表达的, 也不是更高目标的吸收.
> 3. **覆盖的来源 (§3).** 不是上一阶段的对角: 每个闭包在自己的上下文族里从 $\varphi=1$ 重新起步. 所以 `no-growth` 不挡路, 阶段步不需要从对角取数据.
> 4. **编译的否定 (§5).** `no-lift`: $j\sqsubseteq^\mathsf IA\prec^\mathsf IB$ 推不出 $j+1\sqsubseteq^\mathsf IB$. 这堵住了 "对一切 $\eta$ 证 `Goodᶻ`" 的捷径: 值上的弱膨胀成立, 层号上不成立. 所以 $k\ge3$ 必须用 `Goodᴺ` (只在链点处).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件. 本文没有验收节, 因为还没有证书可验收; 全文不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformPending where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (¬_)

open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Ordˢ; Ωˢ; toZ; Goodᶻ; force; force-HS)
open import OCF.Align.UniformS using (≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ʳ; force-≅; toZ-≅; Ωˢ-≅; Ωˢ-refl; ≅ˢ-sym)
open import OCF.Align.Uniform2Base using (Flr; fz; fk; _⊔_; Ev; Run; Ω̂A; ∅ᴿ; flo; cvFlo)
open import OCF.Align.UniformNFBase using (Obs; idO; fo; addo; run; _≈ᵒ_; ≈ᵒ-reflˡ; ≈ᵒ-reflʳ; run-≅)
open import OCF.Align.UniformPendingBase
```

## §1 阶段塔

$P_0=\emptyset^\mathsf R$, $P_{k+1}=$ `Ω̂A 0 P_k`, 即 $\psi_\cdot(\Omega_\Omega\cdot k)$. 地板只含 `fk zero` 的和.

```agda
Fl : ℕ → Flr
Fl zero    = fz
Fl (suc k) = Fl k ⊔ fk zero

Pk : ∀ k → Run (Fl k)
Pk zero    = ∅ᴿ
Pk (suc k) = Ω̂A 0 (Pk k)

pfl-k : ∀ k → PFl (Pk k)
pfl-k zero    = pfl∅
pfl-k (suc k) = pfl-Ω̂ (pfl-k k)
```

## §2 上下文族上的单调增长

上下文族 `C`: 每个层号一个观测, 两两相似, 都满足 `Ctx`. 典型的是 $\psi_0(P_k+\psi_b(P_{k-1}+\cdot))$. `grow` 是 Growth 的 `growth-mono` 的一般形: 只用 `Ω-strict`, 对任意前缀栈, 不读阶段.

```agda
record Fam : Set where
  field
    C   : ∀ φ → Obs φ
    sim′ : ∀ φ φ′ → C φ ≈ᵒ C φ′
    ctx : ∀ φ → Ctx (C φ)
open Fam public

Cert : (F : Fam) → Ordᴵ → Set
Cert F φ = Goodᶻ (toZ (run (C F φ) (Ωˢ φ)))

lv : ∀ {F φ} → Cert F φ → Ordᴵ
lv G = toLevel (force _ G) (force-HS _ G)

grow′ : ∀ F {η a η′} → η ≅ᴵ a → a <ᴵ η′ → (G : Cert F η) (G′ : Cert F η′) → lv {F} G ≺ᴵ lv {F} G′
grow′ F {η} {a} {η′} e q G G′ =
  ≺ᴵ-respˡ (toLevel-≅ (force-HS _ G) (force-HS _ G₀) eq′) (toLevel-≺ (force-HS _ G₀) (force-HS _ G′) (proj₂ L (proj₂ S)))
  where
  L = Ω<ᴱ (≅ᴵ-refl a) q (sim′ F (suc a) η′) G′
  S = Ω-strict a (sim′ F a (suc a)) (ctx F (suc a)) (proj₁ L)
  G₀ = proj₁ S
  eq′ = force-≅ (toZ-≅ (run-≅ (sim′ F η a) (Ωˢ-≅ e))) G G₀

grow : ∀ F {η η′} → η ≺ᴵ η′ → (G : Cert F η) (G′ : Cert F η′) → lv {F} G ≺ᴵ lv {F} G′
grow F (via e q) = grow′ F e q

```

## §3 阶段步: 上下文自身的链生成覆盖

`Cov F φ c`: $\Omega_\varphi$ 在族 $F$ 里的计值有证书, 层号 $\sqsupseteq c$. `PC F η`: Pending 的弹栈覆盖, 但相对上下文族 $F$. **`PC-base`/`PC-step` 对任意 $F$ 成立**: 覆盖不来自上一阶段的对角, 而来自这个闭包自己的链点 ($\varphi=1$ 起步), 所以 `no-growth` 不挡路: 新闭包换了上下文, 链也重新开始.

```agda
NZ : Ordᴵ → Set
NZ zero      = ⊥
NZ (suc _)   = ⊤
NZ (lim _ _) = ⊤

one⊑ : ∀ {i ℓ} → zero <ᴵ ℓ → i <ᴵ ℓ → NZ i → suc zero ⊑ᴵ i
one⊑ z p nz with <ᴵ-dec z p
... | injᵃ r          = s⊑′ r
... | injᵇ (via e ())
... | injᶜ z≅         = ⊥-elim nz

Cov : Fam → Ordᴵ → Ordᴵ → Set
Cov F φ c = Σ (Cert F φ) λ G → c ⊑ᴵ lv {F} G

PC : Fam → Ordᴵ → Set
PC F η = ∀ {i L} → zero <ᴵ L → i <ᴵ L → NZ i → i ≺ᴵ η → Σ Ordᴵ λ φ → Cov F φ (suc i) × φ ⊑ᴵ i

PC-base : ∀ F (G₁ : Cert F (suc zero)) → PC F (lv {F} G₁)
PC-base F G₁ z p nz r = suc zero , (G₁ , s⊑′ r) , one⊑ z p nz

≺→⊑ : ∀ {a b} → a ≺ᴵ b → a ⊑ᴵ b
≺→⊑ h = ⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) (s⊑′ h)

pick : ∀ F {η i b b′} → PC F η → (G : Cert F η) → η ≅ᴵ b → i ≅ᴵ b′ → (∀ {c} → c ⊑ᴵ lv {F} G → Cov F η c) → i ≺ᴵ lv {F} G →
       ∀ {L} → zero <ᴵ L → i <ᴵ L → NZ i → (b′ ≺ᴵ b ⊎ b ≺ᴵ b′ ⊎ b′ ≅ᴵ b) → Σ Ordᴵ λ φ → Cov F φ (suc i) × φ ⊑ᴵ i
pick F pc G eb ei cov r z p nz (injᵃ s) = pc z p nz (≺ᴵ-respˡ ei (≺ᴵ-respʳ s (≅ᴵ-sym eb)))
pick F {η} pc G eb ei cov r z p nz (injᵇ s) = η , cov (s⊑′ r) , ≺→⊑ (≺ᴵ-respˡ eb (≺ᴵ-respʳ s (≅ᴵ-sym ei)))
pick F {η} pc G eb ei cov r z p nz (injᶜ c) = η , cov (s⊑′ r) , ≅ᴵ→⊑ᴵ (≅ᴵ-trans eb (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym ei)))
```

**阶段步.** 给链点的证书 $G$ (层号 $\eta_+$) 与新链点的证书 $G'$, 有 `PC F η₊ → PC F (lvl G′)`; 增长由 `grow`, 覆盖就是 $G'$ 自身. 这里没有 $k$, 没有前缀的阶段, 也不要前一阶段的数据.

```agda
PC-step : ∀ F {η} (G : Cert F η) → η ≺ᴵ lv {F} G → PC F η → PC F (lv {F} G)
PC-step F {η} G (via eb q) pc z p nz r@(via ei q′) =
  pick F pc G eb ei (λ h → G , h) r z p nz (<ᴵ-dec q′ q)

PC-lim : ∀ {F f s} → (∀ n → PC F (f n)) → PC F (lim f s)
PC-lim h z p nz (via e (lim n q)) = h n z p nz (via e q)

Link : ∀ F {η η′} → η ≺ᴵ η′ → (G : Cert F η) (G′ : Cert F η′) → η′ ≅ᴵ lv {F} G → PC F η′ → PC F (lv {F} G′)
Link F {η′ = η′} h G G′ e pc = PC-step F {η = η′} G′ (≺ᴵ-respʳ (≺ᴵ-respˡ e (grow F h G G′)) (≅ᴵ-refl _)) pc
```

## §4 弹栈的支配: 只读上下文

`pop-dom`: 若 $i$ 被族 $F$ 覆盖, 则一切地板 $\sqsupseteq\Omega_\varphi$ 的尾巴 $t$, 在该族的任一相似观测下, 任意证书的层号 $\sqsupseteq i+1$. 上下文可以含目标低于 $i$ 的折叠: 比较发生在**整个栈**上, 不要求地板穿过低目标再生. 这就是 "悬置" 的语义形式, 不需要模式.

```agda
pop-dom : ∀ F {φ c k} {t : Ordˢ k} {O : Obs k} → Cov F φ c → Ωˢ φ ⊑ᴱ t → C F φ ≈ᵒ O → (G′ : Goodᶻ (toZ (run O t))) →
          c ⊑ᴵ toLevel (force _ G′) (force-HS _ G′)
pop-dom F {φ} (G , h) fl o G′ =
  ⊑ᴵ-trans h (⊑ᴵ-trans (≅ᴵ→⊑ᴵ (toLevel-≅ (force-HS _ G) (force-HS _ (proj₁ (fl o G′))) (force-≅ (toZ-≅ (run-≅ (≈ᵒ-reflˡ o) (Ωˢ-refl φ))) G _)))
                       (toLevel-⊑ (force-HS _ _) (force-HS _ G′) (proj₂ (fl o G′))))
```

## §4′ 实例: 对一切 $k$, 同一个族, 以及第 3 阶段才出现的两层上下文

`Top k`: $\psi_0(P_k+\Omega_\varphi)$ 的族 (环境作参数, 只经 `flo`/`cvFlo`). `Nest k`: $\psi_0(P_{k+1}+\psi_b(P_k+\Omega_\varphi))$ 的族: 目标 $b$ 是定值, $\varphi$ 可以远高于 $b$. 当 $k\ge1$ 时这正是 $P_{k+1}$ 的闭包分支在 $\psi_0(P_{k+1}+\cdot)$ 之下的上下文, §6 说明它为什么不是单层 `ColC` 能表达的. 证明只有 `pfl-k`, 不看 $k$ 的值.

```agda
Env : ∀ k → Set
Env k = ∀ φ → Σ Ordᴵ λ ℓ → Ev ℓ (Fl k ⊔ flo φ) × zero <ᴵ ℓ

Top : ∀ k → Env k → Fam
Top k E = record
  { C    = λ φ → fo (flo φ) idO (Pk k) (cvFlo φ) (proj₁ (proj₂ (E φ))) (proj₂ (proj₂ (E φ)))
  ; sim′ = λ φ φ′ → fo idO (PFl.rP (pfl-k k))
  ; ctx  = λ φ → pfl-k k , tt
  }

grow-k : ∀ k (E : Env k) {η η′} → η ≺ᴵ η′ → (G : Cert (Top k E) η) (G′ : Cert (Top k E) η′) → lv {Top k E} G ≺ᴵ lv {Top k E} G′
grow-k k E = grow (Top k E)

record NestEnv (k : ℕ) (b : Ordᴵ) : Set where
  field
    φ₀  : Flr
    cv₀ : ∀ {L} → Ev L φ₀ → Simᴵ b L
    ℓ₀  : Ordᴵ
    ev₀ : Ev ℓ₀ (Fl (suc k) ⊔ φ₀)
    z₀  : zero <ᴵ ℓ₀
    E   : ∀ φ → Σ Ordᴵ λ ℓ → Ev ℓ (Fl k ⊔ flo φ) × b <ᴵ ℓ

Nest : ∀ k b → NestEnv k b → Fam
Nest k b N = record
  { C    = λ φ → fo (flo φ) (fo (NestEnv.φ₀ N) idO (Pk (suc k)) (NestEnv.cv₀ N) (NestEnv.ev₀ N) (NestEnv.z₀ N))
                    (Pk k) (cvFlo φ) (proj₁ (proj₂ (NestEnv.E N φ))) (proj₂ (proj₂ (NestEnv.E N φ)))
  ; sim′ = λ φ φ′ → fo (fo idO (PFl.rP (pfl-k (suc k)))) (PFl.rP (pfl-k k))
  ; ctx  = λ φ → pfl-k k , pfl-k (suc k) , tt
  }
```

## §5 否定: 层号的弱膨胀不能变成界

在值上, $\eta\preceq\mathrm{lvl}\,\psi(P+\Omega_\eta)$ 与 §2 的增长一起给出 "一切 $\eta$ 都被支配", 那样 `Goodᶻ` 的 "一切 $\eta$" 就能证了. 证明停在一步: $j\sqsubseteq^\mathsf IA\prec^\mathsf IB$ **推不出** $j+1\sqsubseteq^\mathsf IB$, 因为 $\cong^\mathsf I$ 对 `lim` 逐点. `no-lift` 是编译的反例: $\omega'=\lim(0,2,4,\dots)\sqsubseteq^\mathsf I\omega\prec^\mathsf I\omega+1$, 但 $\omega'+1\not\sqsubseteq^\mathsf I\omega+1$. 这正是 `Chain.Diag.no-growth` 里的移位. 所以闭包的界必须是链点层号里**字面**的元素 (`sim`), 也就是 `PC`.

```agda
fin : ℕ → Ordᴵ
fin zero    = zero
fin (suc n) = suc (fin n)

fin2 : ℕ → Ordᴵ
fin2 zero    = zero
fin2 (suc n) = suc (suc (fin2 n))

ωᵢ : Ordᴵ
ωᵢ = lim fin (λ n → Sim→⊑ᴵ (λ q → suc q))

ωₑ : Ordᴵ
ωₑ = lim fin2 (λ n → Sim→⊑ᴵ (λ q → suc (suc q)))

dbl : ℕ → ℕ
dbl zero    = zero
dbl (suc n) = suc (suc (dbl n))

e2 : ∀ n → fin2 n ≅ᴵ fin (dbl n)
e2 zero    = z≅
e2 (suc n) = s≅ (s≅ (e2 n))

fin2⊑ωᵢ : ∀ n → fin2 n ⊑ᴵ ωᵢ
fin2⊑ωᵢ n = ⊑ᴵ-trans (≅ᴵ→⊑ᴵ (e2 n)) (Sim→⊑ᴵ (λ q → lim (dbl n) q))

ωₑ⊑ω : ωₑ ⊑ᴵ ωᵢ
ωₑ⊑ω = l⊑ fin2⊑ωᵢ

no-fin : ∀ n → ωₑ ≅ᴵ fin n → ⊥
no-fin zero ()
no-fin (suc n) ()

no-lim-below : ∀ n {x} → x <ᴵ fin n → ωₑ ≅ᴵ x → ⊥
no-lim-below zero ()
no-lim-below (suc n) zero e = no-fin n e
no-lim-below (suc n) (suc q) e = no-lim-below n q e

no-lift : ¬ (∀ {j A B} → j ⊑ᴵ A → A ≺ᴵ B → suc j ⊑ᴵ B)
no-lift H with H {ωₑ} {ωᵢ} {suc ωᵢ} ωₑ⊑ω (via (≅ᴵ-refl ωᵢ) zero)
... | s⊑ (l≅ f) zero with f 1
...   | s≅ ()
no-lift H | s⊑ e (suc (lim n q)) = no-lim-below n q e
```

## §6 结论: 判据、障碍与下一步所需的类型

**阶段无关, 已编译.** `pfl-k`、`grow`、`grow-k`、`Top`、`Nest`、`PC-base`、`PC-step`、`PC-lim`、`Link`、`pop-dom`. 其中没有对 $k$ 的分情形, 也没有逐阶段的支配论证. **但它们都是条件式的:** 都以 `Goodᶻ` 证书 (`Cert`) 为前提. 对 $k\ge2$ 这些证书是否存在未知 (下面第 2 点), 所以在移到 `Goodᴺ` 之前, `grow-k` 等在 $k\ge2$ 处可能是空真的. 一致性是证明形状的一致, 还不是证书的存在. `Link` 的前提 `η′ ≅ᴵ lv G` 就是 "下一层号是上一链点的层号", 与 Pending 的 `Link` 同形, 但对任意上下文族.

**需要逐阶段输入的, 目前的形式.** 没有证明 "没有"; 只是还没到那一步. 能说的是: 上面这些都不要逐阶段输入, 而缺的那一层 (下面) 的设计里 $k$ 只经 `pfl-k` 与前缀值的归纳进入.

**没有做的.** 任务 1 (三层 `Good` 的移植)、任务 2 (统一树上的 $\psi_0(\Omega_\Omega\cdot2)$ 与验收)、任务 3 的证书. 原因: 分析表明直接移植在 $k=3$ 不够 (下述), 于是先做了跨阶段所必需的部分; 这是顺序的选择, 代价是决定性检验在统一形上还没有编译结果.

**为什么 Pending 的三层到 $k=3$ 不够 (分析, 未编译否定).**

1. `Good₊` 的 `bŝ` 与 `bĉ` 对一切 $\eta$ 要分支的好性, `Goodᶻ.gc` 同样. $P_1$ 够用, 因为分支 $\psi^{[]}_b(\Omega_\eta)$ 不弹栈 (`mC`). $P_2$ 的分支弹栈, `Cvd K (suc b′)` 要 $\varphi\sqsubseteq K$ 覆盖一个任意高的 $b'$. 所以 $P_2$ 的分支必须只在链点处要求, 第 0 层必须是 `Goodᴺ`, 非零层的 `bŝ` 要带守卫.
2. `CovΛ P₂` 与 `⊑ᵒ` 都以 `Goodᶻ` 为证书; $P_2$ 在目标 0 的 `Goodᶻ` 要 "一切 $\eta$", 是否成立未知. `⊑ᵒ`、`ColC`、`CovΛ`、`dom-cov` 要改成 `Goodᴺ` 上的版本 (规则是机械的, §2 的 `grow` 这一层也要同样改写; `Goodᴺ` 沿 `≅ᶻ` 的搬运 NotFree 没有写).
3. $\psi_0(P_2+\psi_b(P_1+\Omega_{\eta}))$ 的链 $y_{m+1}=$ 该树 $[\eta:=\mathtt{lvl}\,y_m]$ 里, 闭包界 $b'+1$ ($b\prec b'\prec\eta_m$) 的支配要比较 $\psi_0(P_2+\psi_b(P_1+\Omega_\varphi))$, 即 `Nest` 族的 `Cov`; 全局 `ColC P₂` 的地板只有 $\Omega_b$, 够不到 $b'$. 这是 `PC` 必须相对上下文的原因.

**下一步要的类型 (未编译).** 遗传好树以上下文类 $\mathcal G$ 为下标: `Good 𝓖 x`, 闭包的支配读 `∀ C ∈ 𝓖`, 分支带守卫 `𝓑 η` 与链封闭 (`C ∈ 𝓖 → G₀ 是第 0 点的证书 → C ∈ 𝓑 (lvl G₀)`, 及后继), `limᵢ` 带悬置类的 `tr` 与吸收 `ab` (形同 Pending 的 `biV`). 折叠定理的形式是 `Good 𝓖 x → Good ((Q,i)⁻¹𝓖) (fold Q i x)`, 地板 $\mathcal A(K)$ 对前插折叠封闭, $\mathcal S(K)$ 由 `pop-dom` 读出. 以上是纸面设计, 可能还有未预见的缺口.

**树原生与读记号.** 本文的 `⊑ᴱ`、`Rs`、`Climb`、`PC` 从树的折叠子句推出, 没有读记号; `PC` 的形状取自 Pending. 三层的吸收 `biV` (下一步要用) 是读 `vs`/`occ<` 规则得到的启发, 这一点未变.

**一个未核实的疑点.** NotFree §6 (iii) 说 $\psi^{[\hat\Omega]}_0(\psi^{[\hat\Omega]}_1(\Omega_{\mathtt{lvl}\,\gamma'_2}))$ 没有 `Goodᴺ` 证书, 依据是记号值 (`dip`). `Nest` 与 `grow` 提示树的值可能不随记号坍缩, 那条纸面论证未必成立. 这里只是疑点, 没有编译任何一个方向.
