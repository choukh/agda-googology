> **机械克隆, 验收用.** 由 `ScafLadderZOmegaKBase` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆.** 由 `OmegaKBase` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 多个 $\hat\Omega$ 帧: 记号侧与带前缀引理

> 接 [GoodLBase](GoodLBase.lagda.md) 与 [GoodL](GoodL.lagda.md) §5. 本文是 [OmegaK](OmegaK.lagda.md) 的前半: 把 GoodLBase §11–§12 只为单帧 `ψ1` 写的带前缀引理推广到 $n+1$ 个 $\hat\Omega$ 帧 (对 $n$ 归纳), 并补上记号侧的 $\psi_0(\Omega_\Omega\cdot k)$、$\psi_0(\Omega_\Omega\cdot\omega)$、$\psi_0(\Omega_\Omega^2)$. 决定性检验在 OmegaK.
>
> 结论先说:
>
> 1. **记号 (§1).** $\Omega_\Omega\cdot n+a$ 写成 `ΠΩ n a` ($n$ 个 `ΩΩ` 接在 $a$ 前), $\psi_0(\Omega_\Omega\cdot(n+1)+a)$ 是 `ctxK n a = ctx (ΠΩ n a)`, $\psi_w(\Omega_\Omega\cdot(n+1)+a)$ 是 `ctxwK n w a`. 三个目标项 `tk k` $=\psi_0(\Omega_\Omega\cdot k)$、`tω` $=\psi_0(\psi_\Omega(1))=\psi_0(\Omega_\Omega\cdot\omega)$、`tΩ2` $=\psi_0(\psi_\Omega(\Omega_\Omega))=\psi_0(\Omega_\Omega^2)$ 都是 $\psi_0(\Omega_{\Omega+1})$ 的后代 (`tΩ2 = tO[1]`, `tω = tO[1][0][0]`, `tk k = tω[k]`), 所以 `NF₁` 由 StandardOmega 的 `tO-desc-NF` 一次给出 (`tk-NF`, `tω-NF`, `tΩ2-NF`). 基本列: $\psi_0(\Omega_\Omega\cdot(n+2))[j]=\psi_0(\Omega_\Omega\cdot(n+1)+\Omega_{\delta_{j-1}})$ (`fs-pop0`), $\psi_0(\Omega_\Omega\cdot\omega)[k]=\psi_0(\Omega_\Omega\cdot k)$ (`fs-tω`), $\psi_0(\Omega_\Omega^2)[m]=\psi_0(\psi_\Omega(\Omega_{\gamma_m}))=\psi_0(\Omega_\Omega\cdot\Omega_{\gamma_m})$ (`refl`). 注意最后一个: 链点前缀**不是** $\Omega_\Omega\cdot\gamma_m$ 个 $\hat\Omega$ 帧, 而是单个主项 $\psi_\Omega(\Omega_{\gamma_m})$.
> 2. **栈 (§2).** 纯 $\hat\Omega$ 栈是谓词 `AΩ P` (`Vec` 上的归纳谓词, 不限定各帧的证据). 弹栈子句 `ψᴾ (suc n) … (fΩ̂ z ∷ P) zero` 经 `rebase` 读 `onlyΩ̂ P`, 对抽象的 $P$ 卡住; `pop-eq` 用 `AΩ P` 把它改写成闭包 `popˢ n p z` (剩余栈是 `replicate n` 个新帧). 自相似 `ψK-≅` 对 $n$ 与互模拟推导字典序递归; 它的 `lᵢ≅` 子句照抄 UniformS 的 `with` 写法**过不了停机检查** (报错见 §2), 改为把两个递归调用当 λ 参数传给 `liK` 才过.
> 3. **带前缀引理 (§3–§4).** `PreK₊`/`PreVK`/`PreAK`/`giPreK`/`popLK` (目标 $w\ne0$) 与 `Pre0K₊`/`Pre0VK`/`Pre0AK`/`liLabK`/`foldLabK`/`ŝChainK`/`pop0K` (目标 $0$, 证书与标签一起) 对一切 $n$ 成立. **需要帧数的只有两个弹栈引理**: `popLK (suc m)` 与 `pop0K (suc m)` 的闭包的第 0 点与分支是 $m+1$ 帧的树, 递归调用 `PreVK m` / `Pre0VK m` (帧数下降); `popLK 0`/`pop0K 0` 直接是 GoodLBase 的 `popL`/`pop0ᴸ`. 其余子句与单帧逐字相同, 只把记号前缀 `ΩΩ ∷ b` 换成 `ΠΩ (suc n) b` (交换引理 `cofΠ`/`predΠ`/`fsnΠ`/`fsTΠ`, 对抽象 $n$ 不是定义性的), 出现 `Occ` 往外包 $n+1$ 层 (`OccΠ`). `Goodᴸ`、`gc`、`limᴸ`/`ĉᴸ-mk`、`domᴸ`、`fs-mono₁`、`LabL` (含 `gŝ` 的地板) 全部原样导入, 未改.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZOmegaKBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_) renaming (replicate to replicateV)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev; σ1)
open import OCF.Align.LadderLabZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; ψᴾ;
  Frame; fΩ̂; fT; liftF; liftV; onlyΩ̂; z<suc; H1-pen; H1-fsT; trˢ; tr⁻ˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; Cmp; lt; eq; gt;
              []<; hd<; tl<; lv<; ar<; cofA; cofψ0; cofψ₊) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω)
open import OCF.Align.Bachmann using (fs-gt; pen→<; gt→≤; clash)
open import OCF.Align.Closure using (Pen; fsT₊-pen′)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-pred; NF₁-fsn; walk; walkD; tO-desc-NF)
open import OCF.Align.Standard using (Desc; d₀)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.Stage2 using (ctx; Ωᵗ; tO)
open import OCF.Align.LadderLabZUniformS
open import OCF.Align.LadderLabZStage2Label using (one⁰)
open import OCF.Align.LadderLabZDecoupleBase using (ΩΩ; 1<ctx; ŝ-reflg)
open import OCF.Align.LadderLabZDecouple using (Idx; lvI; Ilt; Ieq; kdI; kdI′; gtν; kdI[]; cofP)
open import OCF.Align.LadderLabZGoodLBase
```

## §1 记号

**前缀.** `ΠΩ n a` $=\Omega_\Omega\cdot n+a$. 定义使 `ctxK n a` $=\psi_0(\Omega_\Omega\cdot(n+1)+a)$ 字面等于 GoodLBase 的 `ctx (ΠΩ n a)`, `ctxK 0` 就是 `ctx`, 所以单帧的结论是 $n=0$ 的特例 (下面两个 `refl`). `tk 0` $=\psi_0(0)=1$.

```agda
ΠΩ : ℕ → T → T
ΠΩ zero    a = a
ΠΩ (suc n) a = ΩΩ ∷ ΠΩ n a

ctxK : ℕ → T → T
ctxK n a = ctx (ΠΩ n a)

ctxwK : ℕ → T → T → T
ctxwK n w a = ctxw w (ΠΩ n a)

_ : ∀ n a → ctxK n a ≡ ψᵗ [] (ΠΩ (suc n) a) ∷ []
_ = λ n a → refl

_ : ∀ a → ctxK 0 a ≡ ctx a
_ = λ a → refl

tk : ℕ → T
tk k = ψᵗ [] (ΠΩ k []) ∷ []

tω : T
tω = ψᵗ [] (ψᵗ Ωᵗ (natT 1) ∷ []) ∷ []

tΩ2 : T
tΩ2 = ψᵗ [] (ψᵗ Ωᵗ (ΩΩ ∷ []) ∷ []) ∷ []
```

**交换引理.** EBO 的 `cof`/`pred`/`fsn`/`fsT` 在和 `x ∷ xs` 上只有当 `xs` 字面是 `_ ∷ _` 时才往下走一步 (`cof (x ∷ xs@(_ ∷ _)) = cof xs`), 所以对抽象的 $n$, `cof (ΠΩ n (y ∷ ys))` 卡住. 下面四条对 $n$ 归纳 (分出 $n=1$ 是为了让 `ΠΩ n (y ∷ ys)` 先展开成 cons); `cofΠ0`/`fsTΠ0` 是尾巴为 $0$ 的版本 ($\Omega_\Omega\cdot(n+1)$ 的共尾度是 $\Omega_1$, $[\theta]=\Omega_\Omega\cdot n+\Omega_\theta$); `ΠΩ-rep` 对上 EBO 规则 4 的 `replicate`.

```agda
cofΠ : ∀ n y ys → cof (ΠΩ n (y ∷ ys)) ≡ cof (y ∷ ys)
cofΠ zero          y ys = refl
cofΠ (suc zero)    y ys = refl
cofΠ (suc (suc n)) y ys = cofΠ (suc n) y ys

predΠ : ∀ n y ys → pred (ΠΩ n (y ∷ ys)) ≡ ΠΩ n (pred (y ∷ ys))
predΠ zero          y ys = refl
predΠ (suc zero)    y ys = refl
predΠ (suc (suc n)) y ys = cong (ΩΩ ∷_) (predΠ (suc n) y ys)

fsnΠ : ∀ n y ys m → fsn (ΠΩ n (y ∷ ys)) m ≡ ΠΩ n (fsn (y ∷ ys) m)
fsnΠ zero          y ys m = refl
fsnΠ (suc zero)    y ys m = refl
fsnΠ (suc (suc n)) y ys m = cong (ΩΩ ∷_) (fsnΠ (suc n) y ys m)

fsTΠ : ∀ n y ys θ → fsT (ΠΩ n (y ∷ ys)) θ ≡ ΠΩ n (fsT (y ∷ ys) θ)
fsTΠ zero          y ys θ = refl
fsTΠ (suc zero)    y ys θ = refl
fsTΠ (suc (suc n)) y ys θ = cong (ΩΩ ∷_) (fsTΠ (suc n) y ys θ)

cofΠ0 : ∀ n → cof (ΠΩ (suc n) []) ≡ cΩ []
cofΠ0 zero    = refl
cofΠ0 (suc n) = cofΠ0 n

fsTΠ0 : ∀ n θ → fsT (ΠΩ (suc n) []) θ ≡ ΠΩ n (Ωt θ)
fsTΠ0 zero    θ = refl
fsTΠ0 (suc n) θ = cong (ΩΩ ∷_) (fsTΠ0 n θ)

OccΠ : ∀ {w a} n → Occ w a → Occ w (ΠΩ n a)
OccΠ zero    o = o
OccΠ (suc n) o = ot (OccΠ n o)

ΠΩ-rep : ∀ k → ΠΩ k [] ≡ replicate k ΩΩ
ΠΩ-rep zero    = refl
ΠΩ-rep (suc k) = cong (ΩΩ ∷_) (ΠΩ-rep k)
```

**单帧引理的 $n$ 帧版.** 每条都是 "Bachmann/Correspond/Closure/Prefix 的一条记号引理, 用于参数 `ΩΩ ∷ ΠΩ n (y ∷ ys)`, 再经交换引理整理成 `ctxwK n w (…)` 形状": `repK` (规则 4, `fs-rep`), `ωK` (规则 5ω, `fs-ω`), `gtK` (规则 6, `fs-gt`; 链 $\gamma$ 换成 `γK`, 即 $\gamma_0=\Omega_\nu$, $\gamma_{m+1}=\psi_\nu(\Omega_\Omega\cdot(n+1)+a[\gamma_m])$, `γK-eq` 把它与 EBO 的 `γT` 对上), `penK` (穿透, `fsT₊-pen′`), `H1K` (Prefix 的 H1). GoodLBase 里这些都直接用原引理, 因为 `ΩΩ ∷ y ∷ ys` 字面是 cons.

```agda
cK : ∀ n {y ys k} → cof (y ∷ ys) ≡ k → cof (ΠΩ (suc n) (y ∷ ys)) ≡ k
cK n {y} {ys} c = trans (cofΠ (suc n) y ys) c

cofK : ∀ n w y ys → cof (ctxwK n w (y ∷ ys)) ≡ cofA w (cof (y ∷ ys))
cofK n w y ys = cong (cofA w) (cofΠ (suc n) y ys)

repK : ∀ n w y ys → cof (y ∷ ys) ≡ c1 → ∀ m →
       fsn (ctxwK n w (y ∷ ys)) m ≡ replicate m (ψᵗ w (ΠΩ (suc n) (pred (y ∷ ys))))
repK n w y ys c m = trans (fs-rep w ΩΩ (ΠΩ n (y ∷ ys)) (cK n c) m)
                          (cong (λ t → replicate m (ψᵗ w t)) (predΠ (suc n) y ys))

ωK : ∀ n w y ys → cof (y ∷ ys) ≡ cω → ∀ m → fsn (ctxwK n w (y ∷ ys)) m ≡ ctxwK n w (fsn (y ∷ ys) m)
ωK n w y ys c m = trans (fs-ω w ΩΩ (ΠΩ n (y ∷ ys)) (cK n c) m)
                        (cong (λ t → ψᵗ w t ∷ []) (fsnΠ (suc n) y ys m))

γK : ℕ → T → T → ℕ → T
γK n a ν zero    = Ωt ν
γK n a ν (suc m) = ctxwK n ν (fsT a (γK n a ν m))

γK-eq : ∀ n y ys ν m → γT (ΠΩ (suc n) (y ∷ ys)) ν m ≡ γK n (y ∷ ys) ν m
γK-eq n y ys ν zero    = refl
γK-eq n y ys ν (suc m) =
  cong (λ t → ψᵗ ν t ∷ []) (trans (cong (fsT (ΠΩ (suc n) (y ∷ ys))) (γK-eq n y ys ν m)) (fsTΠ (suc n) y ys _))

gtK : ∀ n w y ys ν → cof (y ∷ ys) ≡ cΩ ν → cmpᵀ (sucT ν) w ≡ gt → ∀ m →
      fsn (ctxwK n w (y ∷ ys)) m ≡ ctxwK n w (fsT (y ∷ ys) (γK n (y ∷ ys) ν m))
gtK n w y ys ν c em m =
  trans (fs-gt w ΩΩ (ΠΩ n (y ∷ ys)) ν (cK n c) em m)
        (cong (λ t → ψᵗ w t ∷ [])
              (trans (cong (fsT (ΠΩ (suc n) (y ∷ ys))) (γK-eq n y ys ν m)) (fsTΠ (suc n) y ys _)))

penK : ∀ n w y ys ν → cof (y ∷ ys) ≡ cΩ ν → Pen (cmpᵀ (sucT ν) w) → ∀ η →
       fsT (ctxwK n w (y ∷ ys)) η ≡ ctxwK n w (fsT (y ∷ ys) η)
penK n w y ys ν c pn η =
  trans (fsT₊-pen′ w (ΠΩ (suc n) (y ∷ ys)) ν (cof (ΠΩ (suc n) (y ∷ ys))) (cK n c) pn η)
        (cong (λ t → ψᵗ w t ∷ []) (fsTΠ (suc n) y ys η))

H1K : ∀ n x xs y ys → cof (y ∷ ys) ≡ cΩ [] → ∀ θ → fsT (ctxwK n (x ∷ xs) (y ∷ ys)) θ ≡ ctxwK n (x ∷ xs) (fsT (y ∷ ys) θ)
H1K n x xs y ys c θ = trans (H1-fsT x xs ΩΩ (ΠΩ n (y ∷ ys)) (cK n c) θ)
                            (cong (λ t → ψᵗ (x ∷ xs) t ∷ []) (fsTΠ (suc n) y ys θ))
```

**弹栈处的基本列.** `δ n j`: $\psi_0(\Omega_\Omega\cdot(n+2))$ 的第 $j$ 项, $\delta_0=\psi_0(\Omega_\Omega\cdot(n+1)+\Omega_1)$, $\delta_{j+1}=\psi_0(\Omega_\Omega\cdot(n+1)+\Omega_{\delta_j})$ (`fs-pop0`); 目标 $w\ne0$ 时 $\psi_w(\Omega_\Omega\cdot(n+2))$ 共尾度 $\Omega_1$ (`cof-popw`), $[\theta]=\psi_w(\Omega_\Omega\cdot(n+1)+\Omega_\theta)$ (`fsT-popw`). 这正是 "弹出一个 $\hat\Omega$ 后剩 $n+1$ 帧、尾巴 $\Omega_\theta$" 的记号侧.

```agda
δ : ℕ → ℕ → T
δ n zero    = ctxK n (Ωt (natT 1))
δ n (suc j) = ctxK n (Ωt (δ n j))

fs-pop0 : ∀ n j → fsn (ctxK (suc n) []) j ≡ δ n j
fs-pop0 n j = trans (fs-gt [] ΩΩ (ΠΩ (suc n) []) [] (cofΠ0 (suc n)) refl j) (go j)
  where
  B = ΠΩ (suc (suc n)) []
  go : ∀ j → ψᵗ [] (fsT B (γT B [] j)) ∷ [] ≡ δ n j
  go zero    = cong (λ t → ψᵗ [] t ∷ []) (fsTΠ0 (suc n) (natT 1))
  go (suc j) = cong (λ t → ψᵗ [] t ∷ []) (trans (cong (fsT B) (go j)) (fsTΠ0 (suc n) (δ n j)))

cof-pop0 : ∀ n → cof (ctxK (suc n) []) ≡ cω
cof-pop0 n = cong (cofA []) (cofΠ0 (suc n))

fsT-popw : ∀ n x xs θ → fsT (ctxwK (suc n) (x ∷ xs) []) θ ≡ ctxwK n (x ∷ xs) (Ωt θ)
fsT-popw n x xs θ = trans (H1-fsT x xs ΩΩ (ΠΩ (suc n) []) (cofΠ0 (suc n)) θ)
                          (cong (λ t → ψᵗ (x ∷ xs) t ∷ []) (fsTΠ0 (suc n) θ))

cof-popw : ∀ n x xs → cof (ctxwK (suc n) (x ∷ xs) []) ≡ cΩ []
cof-popw n x xs = trans (cong (cofA (x ∷ xs)) (cofΠ0 (suc n))) (H1-pen x xs)
```

**标准形.** 三个目标项都是 $\psi_0(\Omega_{\Omega+1})$ 的后代, 路径由 `refl` 核对, `walkD` 造 `Desc`, `tO-desc-NF` 给 `NF₁`. `tk-NF k` 再经 `fs-tω` 改写.

```agda
tΩ2-walk : walk tO (1 ∷ []) ≡ tΩ2
tΩ2-walk = refl

tω-walk : walk tO (1 ∷ 0 ∷ 0 ∷ []) ≡ tω
tω-walk = refl

fs-tω : ∀ k → fsn tω k ≡ tk k
fs-tω k = trans (fs-ω [] (ψᵗ Ωᵗ (natT 1)) [] refl k)
                (cong (λ t → ψᵗ [] t ∷ []) (trans (fs-rep Ωᵗ (ψᵗ [] []) [] refl k) (sym (ΠΩ-rep k))))

tω-NF : NF₁ tω
tω-NF = tO-desc-NF (walkD d₀ (1 ∷ 0 ∷ 0 ∷ []) (refl , refl , refl , tt))

tΩ2-NF : NF₁ tΩ2
tΩ2-NF = tO-desc-NF (walkD d₀ (1 ∷ []) (refl , tt))

tk-NF : ∀ k → NF₁ (tk k)
tk-NF k = subst NF₁ (fs-tω k) (NF₁-fsn tω-NF refl k)

ctxK-NF : ∀ n → NF₁ (ctxK n [])
ctxK-NF n = tk-NF (suc n)
```

**`refl` 检验 (EBO 的裸值, 与 Python 模拟器 `ebo.py` 的输出逐字一致).** $\psi_0(\Omega_\Omega\cdot3)$ 的前三项是规则 6 在 $\mu=0$ 的链, 前缀 $\Omega_\Omega\cdot2$; $\psi_0(\Omega_\Omega\cdot\omega)$ 的第 $k$ 项是 $\psi_0(\Omega_\Omega\cdot k)$ (第 0 项是 $1$); $\psi_0(\Omega_\Omega^2)$ 的第 $m$ 项是 $\psi_0(\psi_\Omega(\Omega_{\gamma_m}))$, $\gamma_0=1$. 后三个: $\psi_0(\Omega_\Omega^2)[0][0]=\psi_0(\Omega_\Omega\cdot\omega)$, $[0][1]=\psi_0(\psi_\Omega(t_\omega))$, $[0][1][1]=\psi_0(\psi_\Omega(\psi_0(\Omega_\Omega)))$: $\psi_\Omega$ 的参数是**可数的树** $t_\omega$、$t_1$, 不是帧的个数.

```agda
_ : fsn (tk 3) 0 ≡ ψᵗ [] (ΩΩ ∷ ΩΩ ∷ Ωt (natT 1)) ∷ []
_ = refl

_ : fsn (tk 3) 1 ≡ ψᵗ [] (ΩΩ ∷ ΩΩ ∷ Ωt (fsn (tk 3) 0)) ∷ []
_ = refl

_ : fsn (tk 3) 2 ≡ ψᵗ [] (ΩΩ ∷ ΩΩ ∷ Ωt (fsn (tk 3) 1)) ∷ []
_ = refl

_ : fsn tω 0 ≡ natT 1
_ = refl

_ : fsn tω 3 ≡ tk 3
_ = refl

_ : fsn tΩ2 0 ≡ ψᵗ [] (ψᵗ Ωᵗ (Ωt (natT 1)) ∷ []) ∷ []
_ = refl

_ : fsn tΩ2 1 ≡ ψᵗ [] (ψᵗ Ωᵗ (Ωt (fsn tΩ2 0)) ∷ []) ∷ []
_ = refl

_ : walk tΩ2 (0 ∷ 0 ∷ []) ≡ tω
_ = refl

_ : walk tΩ2 (0 ∷ 1 ∷ []) ≡ ψᵗ [] (ψᵗ Ωᵗ tω ∷ []) ∷ []
_ = refl

_ : walk tΩ2 (0 ∷ 1 ∷ 1 ∷ []) ≡ ψᵗ [] (ψᵗ Ωᵗ (tk 1) ∷ []) ∷ []
_ = refl
```

**读法.** $\psi_0(\Omega_\Omega^2)$ 的规则 6 链点 $\psi_0(\psi_\Omega(\Omega_{\gamma_m}))$: 参数 $\psi_\Omega(\Omega_{\gamma_m})=\Omega_\Omega\cdot\Omega_{\gamma_m}$ 是单个主项 (ψ 下标 $\Omega$, 参数不可数), 它的 $\Omega$-基本列 $[\eta]=\psi_\Omega(\eta)$ ($\eta$ 可数), 再往下 $\psi_\Omega(\eta+1)[n]=\psi_\Omega(\eta)\cdot n$. 所以 "帧数" 只在 $\eta$ 是自然数的那一层才出现 ($\psi_\Omega(1)[n]=\Omega_\Omega\cdot n$, 即 $t_\omega$); 一般的链点要的是**以可数树 $\eta$ 为指数的帧** $\Omega_\Omega\cdot\omega^\eta$, 详见 OmegaK §4.

## §2 纯 $\hat\Omega$ 栈

`AΩ P`: 栈 $P$ 的每一帧都是 `fΩ̂` (各帧的证据 $z$ 任意). `onlyA` 给出 Prefix 的 `onlyΩ̂ P ≡ true`; `rebase` 造的栈 (`replicate n (fΩ̂ o)`) 与经 `liftV` 提升的栈仍满足 `AΩ`. **`pop-eq`**: 弹栈子句 `ψᴾ (suc n) p σ (fΩ̂ z ∷ P) zero` 展开为 `ŝ (cb B) …`, `B = rebase′ (onlyΩ̂ P) p z P`; 对抽象 $P$ 卡在 `onlyΩ̂ P`, 用 `rewrite onlyA` 改写后是 `refl`. 剩余栈与 $P$ 的内容无关 (紧的界 `rebase` 重建 $n$ 个新帧), 所以 `popˢ n p z` 只依赖 $n$.

```agda
data AΩ {ℓ : Ordᴵ} : ∀ {n} → Vec (Frame ℓ) n → Set where
  aε : AΩ []
  a∷ : ∀ {n} {z : zero <ᴵ ℓ} {P : Vec (Frame ℓ) n} → AΩ P → AΩ (fΩ̂ z ∷ P)

onlyA : ∀ {ℓ n} {P : Vec (Frame ℓ) n} → AΩ P → onlyΩ̂ P ≡ true
onlyA aε     = refl
onlyA (a∷ {P = P} A) = onlyA {P = P} A

AΩ-rep : ∀ {ℓ} n {z : zero <ᴵ ℓ} → AΩ (replicateV n (fΩ̂ z))
AΩ-rep zero    = aε
AΩ-rep (suc n) = a∷ (AΩ-rep n)

AΩ-lift : ∀ {ℓ ℓ′ n} {ρ : Simᴵ ℓ ℓ′} {P : Vec (Frame ℓ) n} → AΩ P → AΩ (liftV ρ P)
AΩ-lift aε     = aε
AΩ-lift (a∷ A) = a∷ (AΩ-lift A)

popˢ : ∀ n {i ℓ} → i <ᴵ ℓ → zero <ᴵ ℓ → Ordˢ i
popˢ n {i} p z =
  Ord₊ˢ.ŝ (suc i) (ψᴾ n zero (σ1 (z<suc z p)) (replicateV n (fΩ̂ (z<suc z p))) (Ωˢ (suc zero)))
          (λ η e → ψᴾ n {ℓ = Mlev (suc i) η e} (lim 0 zero) (λ q → lim 1 q)
                       (liftV (λ q → lim 0 q) (replicateV n (fΩ̂ (z<suc z p)))) (Ωˢ η))

pop-eq : ∀ {n i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {P : Vec (Frame ℓ) n} → AΩ P →
         ψᴾ (suc n) p σ (fΩ̂ z ∷ P) Ord₊ˢ.zero ≡ popˢ n p z
pop-eq {P = P} A rewrite onlyA {P = P} A = refl
```

**工程注记.** `onlyA (a∷ A) = onlyA A` 在 `--lossy-unification` 下报 `[UnequalTerms] n != (suc n) … when checking that the expression A has type AΩ (fΩ̂ z ∷ P)`: 检查器把 `onlyΩ̂ ?P ≡ true` 与 `onlyΩ̂ (fΩ̂ z ∷ P) ≡ true` 按单射合一, 解出 `?P := fΩ̂ z ∷ P`. 写出 `{P = P}` 即过; `pop-eq` 同理.

**自相似 `ψK-≅`.** UniformS 的 `ψ1-≅` 的 $n$ 帧版, 原因: `liLabK` 的链原子 $c_{m+1}=\psi^{P}_0(f\,c_m)$ 要 `Atomᴸ` 的第一分量 $c_{m+1}\cong^\mathsf s c_{m+1}$. 弹栈情形两边经 `pop-eq` 改写成 `ŝ≅`, 第 0 点与分支递归到 $n$ 帧 (栈换成 `replicate`/`liftV`, 所以陈述必须对两个**不同的** `AΩ` 栈); 其余子句对推导结构递归, $n$ 不变.

**否定 (编译报错).** `lᵢ≅` 子句照抄 `ψ1-≅` 的 `with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′` 写法:

    [TerminationIssue]
    Termination checking failed for the following functions:
      ψK-≅
    Problematic calls:
      ψK-≅ (suc n) A A′ ei (lᵢ≅ e h) | <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
      ψK-≅ n (AΩ-lift (AΩ-rep n)) (AΩ-lift (AΩ-rep n)) ei (Ωˢ-≅ eη)
      OCF.Align.LadderLabZOmegaKBase.chain m
      ψK-≅ (suc n) A A′ e (h x y (≅→Rˢ (<→◃ q) d))

单帧时没有弹栈递归, 只有推导下降, 所以 `with` 生成的辅助函数不碍事; 加上 "$n$ 降、推导任意" 的调用后, 字典序 ($n$, 推导) 在 `with` 辅助函数的参数排列里找不到. 改为 `liK`: 两个递归调用 (目标 $(p,p')$ 与链目标 $(\sigma q,\sigma' q')$) 在主函数体里写成 λ, 作为参数传入, 一次通过.

```agda
liK : ∀ n {i i′ k₁ ℓ₁ k₂ ℓ₂ j j′} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂}
      {P : Vec (Frame ℓ₁) (suc n)} {P′ : Vec (Frame ℓ₂) (suc n)}
      {q : j <ᴵ k₁} {q′ : j′ <ᴵ k₂} {f : Uˢ j (<→◃ q) → Ordˢ k₁} {g : Uˢ j′ (<→◃ q′) → Ordˢ k₂} →
      i ≅ᴵ i′ → j ≅ᴵ j′ →
      (∀ (x : Ordˢ j) (y : Ordˢ j′) → Rˢ j (<→◃ q) (intoˢ (<→◃ q) x) y →
         ψᴾ (suc n) p σ P (f (intoˢ (<→◃ q) x)) ≅ˢ ψᴾ (suc n) p′ σ′ P′ (g (intoˢ (<→◃ q′) y))) →
      (∀ (x : Ordˢ j) (y : Ordˢ j′) → Rˢ j (<→◃ q) (intoˢ (<→◃ q) x) y →
         ψᴾ (suc n) (σ q) σ P (f (intoˢ (<→◃ q) x)) ≅ˢ ψᴾ (suc n) (σ′ q′) σ′ P′ (g (intoˢ (<→◃ q′) y))) →
      ψᴾ (suc n) p σ P (Ord₊ˢ.limᵢ q f) ≅ˢ ψᴾ (suc n) p′ σ′ P′ (Ord₊ˢ.limᵢ q′ g)
ψK-≅ : ∀ n {i i′ k₁ ℓ₁ k₂ ℓ₂} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂}
       {P : Vec (Frame ℓ₁) n} {P′ : Vec (Frame ℓ₂) n} → AΩ P → AΩ P′ →
       {a : Ordˢ k₁} {b : Ordˢ k₂} → i ≅ᴵ i′ → a ≅ˢ b → ψᴾ n p σ P a ≅ˢ ψᴾ n p′ σ′ P′ b
ψK-≅ zero aε aε ei e = ψ0-≅ ei e
ψK-≅ (suc n) {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} (a∷ {z = z} {P = P₁} A) (a∷ {z = z′} {P = P₁′} A′) ei z≅ =
  subst₂ _≅ˢ_ (sym (pop-eq {p = p} {σ = σ} {z = z} {P = P₁} A)) (sym (pop-eq {p = p′} {σ = σ′} {z = z′} {P = P₁′} A′))
         (ŝ≅ (kd-≅ ei) (s≅ ei) (ψK-≅ n (AΩ-rep n) (AΩ-rep n) ei (Ωˢ-refl (suc zero)))
             (λ η e η′ e′ eη → ψK-≅ n (AΩ-lift (AΩ-rep n)) (AΩ-lift (AΩ-rep n)) ei (Ωˢ-≅ eη)))
ψK-≅ (suc n) A A′ ei (s≅ e) = l≅ (iter-R _≅ˢ_ (λ e′ → addˢ-≅ (kd-≅ ei) (ψK-≅ (suc n) A A′ ei e) e′) z≅)
ψK-≅ (suc n) A A′ ei (l≅ h) = l≅ (λ m → ψK-≅ (suc n) A A′ ei (h m))
ψK-≅ (suc n) A A′ ei (upˡ {r = zero} e)   = ψK-≅ (suc n) A A′ ei e
ψK-≅ (suc n) A A′ ei (upˡ {r = self m} e) = ψK-≅ (suc n) A A′ ei e
ψK-≅ (suc n) A A′ ei (upʳ {r = zero} e)   = ψK-≅ (suc n) A A′ ei e
ψK-≅ (suc n) A A′ ei (upʳ {r = self m} e) = ψK-≅ (suc n) A A′ ei e
ψK-≅ (suc n) {k₁ = zero}    {k₂ = zero}    A A′ ei (ŝ≅ k ec et eg) =
  ĉ≅ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (ψK-≅ (suc n) A A′ ei et)
     (λ η e η′ e′ eη → ψK-≅ (suc n) A A′ ei (eg η e η′ e′ eη))
ψK-≅ (suc n) {k₁ = zero}    {k₂ = suc _}   A A′ ei (ŝ≅ k ec et eg) = ⊥-elim (tf k)
ψK-≅ (suc n) {k₁ = zero}    {k₂ = lim _ _} A A′ ei (ŝ≅ k ec et eg) = ⊥-elim (tf k)
ψK-≅ (suc n) {k₁ = suc _}   {k₂ = zero}    A A′ ei (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
ψK-≅ (suc n) {k₁ = lim _ _} {k₂ = zero}    A A′ ei (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
ψK-≅ (suc n) {k₁ = suc _}   {k₂ = suc _}   A A′ ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψK-≅ (suc n) A A′ ei et) (λ η e η′ e′ eη → ψK-≅ (suc n) A A′ ei (eg η e η′ e′ eη))
ψK-≅ (suc n) {k₁ = suc _}   {k₂ = lim _ _} A A′ ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψK-≅ (suc n) A A′ ei et) (λ η e η′ e′ eη → ψK-≅ (suc n) A A′ ei (eg η e η′ e′ eη))
ψK-≅ (suc n) {k₁ = lim _ _} {k₂ = suc _}   A A′ ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψK-≅ (suc n) A A′ ei et) (λ η e η′ e′ eη → ψK-≅ (suc n) A A′ ei (eg η e η′ e′ eη))
ψK-≅ (suc n) {k₁ = lim _ _} {k₂ = lim _ _} A A′ ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψK-≅ (suc n) A A′ ei et) (λ η e η′ e′ eη → ψK-≅ (suc n) A A′ ei (eg η e η′ e′ eη))
ψK-≅ (suc n) A A′ ei (ĉ≅ ec dt dg eo eO) =
  ĉ≅ ec dt dg (ψK-≅ (suc n) A A′ ei eo) (λ η e η′ e′ eη → ψK-≅ (suc n) A A′ ei (eO η e η′ e′ eη))
ψK-≅ (suc n) {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} {P = P} {P′ = P′} A A′ ei (lᵢ≅ {p = q} {q = q′} {f = f} {g = g} e h) =
  liK n {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} {P = P} {P′ = P′} {q = q} {q′ = q′} {f = f} {g = g} ei e
      (λ x y d → ψK-≅ (suc n) {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} A A′ ei (h x y d))
      (λ x y d → ψK-≅ (suc n) {p = σ q} {σ = σ} {p′ = σ′ q′} {σ′ = σ′} A A′ e (h x y d))

liK n {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} {P = P} {P′ = P′} {q = q} {q′ = q′} {f = f} {g = g} ei e rec recC
  with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ u v → ψᴾ (suc n) p σ P (f (intoˢ (<→◃ q) (tr⁻ˢ e₁ u))) ≅ˢ ψᴾ (suc n) p′ σ′ P′ (g (intoˢ (<→◃ q′) (tr⁻ˢ e₂ v))))
         (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-intoˢ (<→◃ r₂) y))
         (rec _ _ (≅→Rˢ (<→◃ q) (tr⁻ˢ-≅ e₁ (≅-tr⁻ˢ e₂ (R→≅ˢ (<→◃ r₁) d)))))
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c  = ⊥-elim (clash₂ e ei r c)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c | injᵃ r  = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c)
... | injᵇ _ | injᵇ _  = l≅ (λ m → rec _ _ (≅→Rˢ (<→◃ q) (chain m)))
  where chain = iter-R _≅ˢ_ (λ d → recC _ _ (≅→Rˢ (<→◃ q) d)) (Ωˢ-≅ e)
... | injᵇ _ | injᶜ _  = l≅ (λ m → rec _ _ (≅→Rˢ (<→◃ q) (chain m)))
  where chain = iter-R _≅ˢ_ (λ d → recC _ _ (≅→Rˢ (<→◃ q) d)) (Ωˢ-≅ e)
... | injᶜ _ | injᵇ _  = l≅ (λ m → rec _ _ (≅→Rˢ (<→◃ q) (chain m)))
  where chain = iter-R _≅ˢ_ (λ d → recC _ _ (≅→Rˢ (<→◃ q) d)) (Ωˢ-≅ e)
... | injᶜ _ | injᶜ _  = l≅ (λ m → rec _ _ (≅→Rˢ (<→◃ q) (chain m)))
  where chain = iter-R _≅ˢ_ (λ d → recC _ _ (≅→Rˢ (<→◃ q) d)) (Ωˢ-≅ e)
```

`chainK`/`fold1K`/`pen1K`: DecoupleBase 的 `chain1`/`fold1`/`pen1` 对任意栈 (证明不看栈, 只看 `<ᴵ-dec`).

```agda
chainK : ∀ {n j k ℓ} (σ : Simᴵ k ℓ) (P : Vec (Frame ℓ) n) (q : j <ᴵ k) (f : Uˢ j (<→◃ q) → Ordˢ k) → ℕ → Ordˢ j
chainK {n} {j} σ P q f = iter (λ x → ψᴾ n (σ q) σ P (f (intoˢ (<→◃ q) x))) (Ωˢ j)

chainK-≅ : ∀ {n j k k′ ℓ} {σ : Simᴵ k ℓ} {P : Vec (Frame ℓ) n} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} {b : Ordˢ k′} →
           AΩ P → Ord₊ˢ.limᵢ q f ≅ˢ b → ∀ m → chainK σ P q f m ≅ˢ chainK σ P q f m
chainK-≅ {j = j} A e zero    = Ωˢ-refl j
chainK-≅ {n} {j} A e (suc m) = ψK-≅ n A A (≅ᴵ-refl j) (i-respˢ e (chainK-≅ A e m))

fold1K : ∀ {n i k ℓ j} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {P : Vec (Frame ℓ) n} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
         (i ≺ᴵ j) ⊎ (i ≅ᴵ j) →
         ψᴾ n p σ P (Ord₊ˢ.limᵢ q f) ≡ Ord₊ˢ.lim (λ m → ψᴾ n p σ P (f (intoˢ (<→◃ q) (chainK σ P q f m))))
fold1K {p = p} {σ = σ} {q = q} h with <ᴵ-dec (σ q) p
... | injᵃ s = ⊥-elim (clash s h)
... | injᵇ _ = refl
... | injᶜ _ = refl

pen1K : ∀ {n i k ℓ j N} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {P : Vec (Frame ℓ) n} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        j ≅ᴵ N → N ≺ᴵ i →
        Σ Ordᴵ λ j′ → Σ (j ≅ᴵ j′) λ e → Σ (j′ <ᴵ i) λ r →
        ψᴾ n p σ P (Ord₊ˢ.limᵢ q f) ≡ Ord₊ˢ.limᵢ r (λ y → ψᴾ n p σ P (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))))
pen1K {p = p} {σ = σ} {q = q} ej νi with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = _ , e , r , refl
... | injᵇ s = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ (≺ᴵ-trans νi s) ej))
... | injᶜ c = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ νi (≅ᴵ-trans (≅ᴵ-sym c) ej)))
```

## §3 带前缀的 $\psi_w$, 目标 $w\ne0$, $n+1$ 个帧

GoodLBase §11 的 `popL`/`giPreL`/`PreAL`/`PreVL`/`PreL₊` 的 $n$ 帧版. 结论 `LabL₊ i Ll (ψᴾ (suc n) p σ P X) (ctxwK n w b)`, $P$ 满足 `AΩ`.

**弹栈 `popLK`, 唯一用到帧数的地方.** $n=0$: 就是 `popL` (`ψᴾ 1 … (fΩ̂ z ∷ [])` 与 `ψ1` 定义性相同). $n=m+1$: 经 `pop-eq` 成为闭包 `ŝ (suc i) t₀ g`, $t_0=\psi^{[\hat\Omega]^{m+1}}_w(\Omega_1)$, $g\,\eta=\psi^{[\hat\Omega]^{m+1}}_w(\Omega_\eta)$, 都是 $m+1$ 帧的树, 由**递归** `PreVK m` 标 (`LabL-Ω` 给尾巴 $\Omega_1$/$\Omega_{\mathtt{lvl}\,Y}$ 的标签), 记号侧 `fsT-popw`. `gŝ` 行的地板与单帧完全相同: 下标 $w$ 与 `Iw`, 界 $i+1\sqsubseteq^\mathsf I\mathtt{lvl}\,w+1$, $t[\theta]=\psi_w(\cdots)$ 的首项下标就是 $w$ (`oh`). 这里 $t[\theta]$ 仍带 $m+1$ 个 $\hat\Omega$: 地板与帧数无关.

```agda
popLK  : ∀ n {i k ℓ w} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {P : Vec (Frame ℓ) (suc n)} → AΩ P → (Iw : Idx w) → i ≅ᴵ lvI Iw →
         kd i ≡ false → LabL₊ i Ll (ψᴾ (suc n) p σ P Ord₊ˢ.zero) (ctxwK n w [])
PreAK  : ∀ n {ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ zero ℓ} {P : Vec (Frame ℓ) (suc n)} {X : Ordˢ zero} {b} → AΩ P →
         (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → Lab0ᴸ X b → LabL₊ i Ll (ψᴾ (suc n) p σ P X) (ctxwK n w b)
PreVK  : ∀ n {k ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {P : Vec (Frame ℓ) (suc n)} {X : Ordˢ k} {b} → AΩ P →
         (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → LabL X b → LabL₊ i Ll (ψᴾ (suc n) p σ P X) (ctxwK n w b)
PreK₊  : ∀ n {k ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {P : Vec (Frame ℓ) (suc n)} {X : Ordˢ k} {b} → AΩ P →
         (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → LabL₊ k Ll X b → LabL₊ i Ll (ψᴾ (suc n) p σ P X) (ctxwK n w b)

popLK zero {p = p} {σ = σ} (a∷ {z = z} aε) Iw ei ki = popL {p = p} {σ = σ} {z = z} Iw ei ki
popLK (suc n) {w = []} A Iw ei ki = ⊥-elim (tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki)))
popLK (suc n) {i = i} {w = x ∷ xs} {p = p} {σ = σ} (a∷ {z = z} {P = P₁} A₁) Iw ei ki =
  subst (λ W → LabL₊ i Ll W (ctxwK (suc n) (x ∷ xs) [])) (sym (pop-eq {p = p} {σ = σ} {z = z} {P = P₁} A₁))
    (gŝ ki (cof-popw n x xs) Iw (⊑ᴵ-≅ʳ ⊑ᴵ-refl (s≅ ei)) (λ θ → subst (Occ (x ∷ xs)) (sym (fsT-popw n x xs θ)) oh)
        (subst (LabL₊ _ Ll _) (sym (fsT-popw n x xs (natT 1)))
               (PreVK n {p = zero} {σ = σ1 (z<suc z p)} {P = replicateV (suc n) (fΩ̂ (z<suc z p))} (AΩ-rep (suc n))
                      Iw ei ki (LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _))))
        (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (fsT-popw n x xs θ))
               (PreVK n {p = lim 0 zero} {σ = λ q → lim 1 q}
                      {P = liftV (λ q → lim 0 q) (replicateV (suc n) (fΩ̂ (z<suc z p)))} (AΩ-lift (AΩ-rep (suc n)))
                      Iw ei ki (LabL-Ω Y hY lY nθ (≅ᴵ-refl _)))))
```

`giPreK`: `giPreL` 逐字, 记号引理换成 `penK`/`gtK`/`cofK`, 链标签 `γK n (y ∷ ys) ν`.

```agda
giPreK : ∀ n {k ℓ i w ν j y ys} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {P : Vec (Frame ℓ) (suc n)} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
         (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
         (rec : ∀ η (x : Ordˢ j) → LabL x η → LabL₊ i Ll (ψᴾ (suc n) p σ P (f (intoˢ (<→◃ q) x))) (ctxwK n w (fsT (y ∷ ys) η))) →
         (recC : kd j ≡ false → ∀ η (x : Ordˢ j) → LabL x η →
                 LabL₊ j Ll (ψᴾ (suc n) (σ q) σ P (f (intoˢ (<→◃ q) x))) (ctxwK n ν (fsT (y ∷ ys) η))) →
         LabL₊ i Ll (ψᴾ (suc n) p σ P (Ord₊ˢ.limᵢ q f)) (ctxwK n w (y ∷ ys))
giPreK n {i = i} {w = w} {ν = ν} {j = j} {y = y} {ys = ys} {p = p} {σ = σ} {P = P} {q = q} {f = f} Iw ei ki c Iν ej rec recC =
  go (cmpᵀ (sucT ν) w) refl
  where
  pen : Pen (cmpᵀ (sucT ν) w) → LabL₊ i Ll (ψᴾ (suc n) p σ P (Ord₊ˢ.limᵢ q f)) (ctxwK n w (y ∷ ys))
  pen pn with pen1K {p = p} {σ = σ} {P = P} {q = q} {f = f} (≅ᴵ-refl j)
                    (≺ᴵ-respʳ (≺ᴵ-respˡ ej (Ilt Iν Iw (pen→< ν w pn))) (≅ᴵ-sym ei))
  ... | j′ , e , r , eqn =
    subst (λ W → LabL₊ i Ll W (ctxwK n w (y ∷ ys))) (sym eqn)
          (gi cofE Iν (≅ᴵ-trans (≅ᴵ-sym e) ej)
              (λ η x l → subst (λ v → LabL₊ i Ll (ψᴾ (suc n) p σ P (f (intoˢ (<→◃ q) (tr⁻ˢ e v)))) (fsT (ctxwK n w (y ∷ ys)) η))
                               (sym (out-intoˢ (<→◃ r) x))
                               (subst (LabL₊ i Ll _) (sym (penK n w y ys ν c pn η))
                                      (rec η (tr⁻ˢ e x) (LabL-tr⁻ e (Ll→ (<→◃ r) l))))))
    where
    cofE : cof (ctxwK n w (y ∷ ys)) ≡ cΩ ν
    cofE = trans (cofK n w y ys) (trans (cong (cofA w) c) (cofP pn))
  ne-w : w ≡ [] → ⊥
  ne-w refl = tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki))
  fold : cmpᵀ (sucT ν) w ≡ gt → LabL₊ i Ll (ψᴾ (suc n) p σ P (Ord₊ˢ.limᵢ q f)) (ctxwK n w (y ∷ ys))
  fold em =
    subst (λ W → LabL₊ i Ll W (ctxwK n w (y ∷ ys))) (sym (fold1K {p = p} {σ = σ} {P = P} {q = q} {f = f} ij))
          (gl (trans (cofK n w y ys) (trans (cong (cofA w) c) (cong (cofψ₊ w ν) em)))
              (λ m → subst (LabL₊ i Ll _) (sym (gtK n w y ys ν c em m)) (rec _ _ (chainL m))))
    where
    gev : (lvI Iw ≺ᴵ lvI Iν) ⊎ (lvI Iw ≅ᴵ lvI Iν)
    gev with gt→≤ ν w em
    ... | inj₁ pw   = inj₁ (Ilt Iw Iν pw)
    ... | inj₂ refl = inj₂ (Ieq Iw Iν)
    ij : (i ≺ᴵ j) ⊎ (i ≅ᴵ j)
    ij with gev
    ... | inj₁ s  = inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ ei s) (≅ᴵ-sym ej))
    ... | inj₂ c′ = inj₂ (≅ᴵ-trans ei (≅ᴵ-trans c′ (≅ᴵ-sym ej)))
    kj : kd j ≡ false
    kj = trans (kd-≅ ej) (kdI′ Iν (gtν em ne-w))
    chainL : ∀ m → LabL (chainK σ P q f m) (γK n (y ∷ ys) ν m)
    chainL zero    = LabL-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
    chainL (suc m) = frL₊ kj (recC kj _ _ (chainL m))
  go : ∀ m → cmpᵀ (sucT ν) w ≡ m → LabL₊ i Ll (ψᴾ (suc n) p σ P (Ord₊ˢ.limᵢ q f)) (ctxwK n w (y ∷ ys))
  go lt em = pen (inj₁ em)
  go eq em = pen (inj₂ em)
  go gt em = fold em
```

`PreAK`/`PreVK`/`PreK₊`: `PreAL`/`PreVL`/`PreL₊` 逐字, 只有 `gz`/`lz` 改调 `popLK n`, 记号引理换成 `repK`/`ωK`/`H1K`/`cofK`, `gŝ` 的出现 `od (ot o)` 换成 `od (OccΠ (suc n) o)`.

```agda
PreAK n {b = []} A Iw ei ki (lz c) = popLK n A Iw ei ki
PreAK n {b = y ∷ ys} A Iw ei ki (lz c) = ⊥-elim (cof-ne y ys c)
PreAK n {b = []} A Iw ei ki (ls () l)
PreAK n {w = w} {p = p} {σ = σ} {P = P} {b = y ∷ ys} A Iw ei ki (ls c l) =
  gl (trans (cofK n w y ys) (cong (cofA w) c))
     (λ m → subst (LabL₊ _ Ll _) (sym (repK n w y ys c m)) (LRep ki (PreAK n {p = p} {σ = σ} {P = P} A Iw ei ki l) m))
PreAK n {b = []} A Iw ei ki (ll () h)
PreAK n {w = w} {p = p} {σ = σ} {P = P} {b = y ∷ ys} A Iw ei ki (ll c h) =
  gl (trans (cofK n w y ys) (cong (cofA w) c))
     (λ m → subst (LabL₊ _ Ll _) (sym (ωK n w y ys c m)) (PreAK n {p = p} {σ = σ} {P = P} A Iw ei ki (h m)))
PreAK n {b = []} A Iw ei ki (lŝ₀ () K h₀ hk)
PreAK n {w = w} {p = p} {σ = σ} {P = P} {b = y ∷ ys} A Iw ei ki (lŝ₀ c K h₀ hk) =
  gĉ (trans (cofK n w y ys) (cong (cofA w) c)) K
     (subst (LabL₊ _ Ll _) (sym (ωK n w y ys c 0)) (PreAK n {p = p} {σ = σ} {P = P} A Iw ei ki h₀))
     (λ m → subst (LabL₊ _ Ll _) (sym (ωK n w y ys c (suc m))) (PreAK n {p = p} {σ = σ} {P = P} A Iw ei ki (hk m)))
PreAK n {b = []} A Iw ei ki (lĉ () K h₀ hk)
PreAK n {w = w} {p = p} {σ = σ} {P = P} {b = y ∷ ys} A Iw ei ki (lĉ c K h₀ hk) =
  gĉ (trans (cofK n w y ys) (cong (cofA w) c)) K
     (subst (LabL₊ _ Ll _) (sym (ωK n w y ys c 0)) (PreAK n {p = p} {σ = σ} {P = P} A Iw ei ki h₀))
     (λ m → subst (LabL₊ _ Ll _) (sym (ωK n w y ys c (suc m))) (PreAK n {p = p} {σ = σ} {P = P} A Iw ei ki (hk m)))

PreVK n {k = zero}    {p = p} {σ = σ} {P = P} A Iw ei ki at = PreAK n {p = p} {σ = σ} {P = P} A Iw ei ki (atomL at)
PreVK n {k = suc _}   {p = p} {σ = σ} {P = P} A Iw ei ki h  = PreK₊ n {p = p} {σ = σ} {P = P} A Iw ei ki h
PreVK n {k = lim _ _} {p = p} {σ = σ} {P = P} A Iw ei ki h  = PreK₊ n {p = p} {σ = σ} {P = P} A Iw ei ki h

PreK₊ n {b = []} A Iw ei ki (gz c) = popLK n A Iw ei ki
PreK₊ n {b = y ∷ ys} A Iw ei ki (gz c) = ⊥-elim (cof-ne y ys c)
PreK₊ n {b = []} A Iw ei ki (gs () l)
PreK₊ n {w = w} {p = p} {σ = σ} {P = P} {b = y ∷ ys} A Iw ei ki (gs c l) =
  gl (trans (cofK n w y ys) (cong (cofA w) c))
     (λ m → subst (LabL₊ _ Ll _) (sym (repK n w y ys c m)) (LRep ki (PreK₊ n {p = p} {σ = σ} {P = P} A Iw ei ki l) m))
PreK₊ n {b = []} A Iw ei ki (gl () h)
PreK₊ n {w = w} {p = p} {σ = σ} {P = P} {b = y ∷ ys} A Iw ei ki (gl c h) =
  gl (trans (cofK n w y ys) (cong (cofA w) c))
     (λ m → subst (LabL₊ _ Ll _) (sym (ωK n w y ys c m)) (PreK₊ n {p = p} {σ = σ} {P = P} A Iw ei ki (h m)))
PreK₊ n {p = p} {σ = σ} {P = P} A Iw ei ki (gu {r = zero} h)   = PreVK n {p = p} {σ = λ q → σ (suc q)} {P = P} A Iw ei ki h
PreK₊ n {p = p} {σ = σ} {P = P} A Iw ei ki (gu {r = self m} h) = PreVK n {p = p} {σ = λ q → σ (lim m q)} {P = P} A Iw ei ki h
PreK₊ n {b = []} A Iw ei ki (gi () Iν ej h)
PreK₊ n {p = p} {σ = σ} {P = P} {b = y ∷ ys} A Iw ei ki (gi {q = q} {f = f} c Iν ej h) =
  giPreK n {p = p} {σ = σ} {P = P} {q = q} {f = f} Iw ei ki c Iν ej
         (λ η x l → PreK₊ n {p = p} {σ = σ} {P = P} A Iw ei ki (h η x (→Ll (<→◃ q) l)))
         (λ kj η x l → PreK₊ n {p = σ q} {σ = σ} {P = P} A Iν ej kj (h η x (→Ll (<→◃ q) l)))
PreK₊ n {b = []} A Iw ei ki (gĉ () K h₀ hk)
PreK₊ n {w = w} {p = p} {σ = σ} {P = P} {b = y ∷ ys} A Iw ei ki (gĉ c K h₀ hk) =
  gĉ (trans (cofK n w y ys) (cong (cofA w) c)) K
     (subst (LabL₊ _ Ll _) (sym (ωK n w y ys c 0)) (PreK₊ n {p = p} {σ = σ} {P = P} A Iw ei ki h₀))
     (λ m → subst (LabL₊ _ Ll _) (sym (ωK n w y ys c (suc m))) (PreK₊ n {p = p} {σ = σ} {P = P} A Iw ei ki (hk m)))
PreK₊ n {k = zero} A Iw ei ki (gŝ () c Ib bb ob h₀ hg)
PreK₊ n {k = suc _} {w = []} A Iw ei ki (gŝ kk c Ib bb ob h₀ hg) = ⊥-elim (tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki)))
PreK₊ n {k = suc _} {w = x ∷ xs} {b = []} A Iw ei ki (gŝ kk () Ib bb ob h₀ hg)
PreK₊ n {k = suc _} {w = x ∷ xs} {p = p} {σ = σ} {P = P} {b = y ∷ ys} A Iw ei ki (gŝ kk c Ib bb ob h₀ hg) =
  gŝ ki (trans (cofK n (x ∷ xs) y ys) (trans (cong (cofA (x ∷ xs)) c) (H1-pen x xs))) Ib bb
     (λ θ → subst (Occ _) (sym (H1K n x xs y ys c θ)) (od (OccΠ (suc n) (ob θ))))
     (subst (LabL₊ _ Ll _) (sym (H1K n x xs y ys c (natT 1))) (PreK₊ n {p = p} {σ = σ} {P = P} A Iw ei ki h₀))
     (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1K n x xs y ys c θ))
                                  (PreK₊ n {p = p} {σ = σ} {P = P} A Iw ei ki (hg θ Y hY lY nθ lt e)))
PreK₊ n {k = lim _ _} {w = []} A Iw ei ki (gŝ kk c Ib bb ob h₀ hg) = ⊥-elim (tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki)))
PreK₊ n {k = lim _ _} {w = x ∷ xs} {b = []} A Iw ei ki (gŝ kk () Ib bb ob h₀ hg)
PreK₊ n {k = lim _ _} {w = x ∷ xs} {p = p} {σ = σ} {P = P} {b = y ∷ ys} A Iw ei ki (gŝ kk c Ib bb ob h₀ hg) =
  gŝ ki (trans (cofK n (x ∷ xs) y ys) (trans (cong (cofA (x ∷ xs)) c) (H1-pen x xs))) Ib bb
     (λ θ → subst (Occ _) (sym (H1K n x xs y ys c θ)) (od (OccΠ (suc n) (ob θ))))
     (subst (LabL₊ _ Ll _) (sym (H1K n x xs y ys c (natT 1))) (PreK₊ n {p = p} {σ = σ} {P = P} A Iw ei ki h₀))
     (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1K n x xs y ys c θ))
                                  (PreK₊ n {p = p} {σ = σ} {P = P} A Iw ei ki (hg θ Y hY lY nθ lt e)))
```

**读法.** 停机一次通过. 互递归 `popLK (suc m) → PreVK m → PreK₊ m → popLK m`: 帧数 $n$ 是每个函数的第一个显式参数, 检查器自己找到 ($n$, 推导) 的字典序. 与单帧版相比, 唯一新增的调用边是弹栈处 $n$ 下降的那一条.

## §4 带前缀的 $\psi_0$, $n+1$ 个帧: 证书与标签一起

GoodLBase §12 的 `Pre0Vᴸ`/`Pre0L₊ᴸ` 的 $n$ 帧版, 结论 `Σ (Goodᴸ (toZ (ψᴾ (suc n) p σ P x))) λ G → Lab (forceᴸ _ G) (ctxK n a)`. 先是两个 `NF₁` 小引理 (链点与 $\omega$-列项, 即 DecoupleBase 的 `nfγ`/`nfω`).

```agda
cofωK : ∀ n {y ys} → cof (y ∷ ys) ≡ cΩ [] → cof (ctxK n (y ∷ ys)) ≡ cω
cofωK n {y} {ys} c = trans (cofK n [] y ys) (cong (cofA []) c)

nfγK : ∀ n {y ys} → NF₁ (ctxK n (y ∷ ys)) → (c : cof (y ∷ ys) ≡ cΩ []) → ∀ m →
       NF₁ (ctxK n (fsT (y ∷ ys) (γK n (y ∷ ys) [] m)))
nfγK n {y} {ys} nu c m = subst NF₁ (gtK n [] y ys [] c refl m) (NF₁-fsn nu (cofωK n c) m)

nfωK : ∀ n {y ys} → NF₁ (ctxK n (y ∷ ys)) → (c : cof (y ∷ ys) ≡ cω) → ∀ m → NF₁ (ctxK n (fsn (y ∷ ys) m))
nfωK n {y} {ys} nu c m = subst NF₁ (ωK n [] y ys c m) (NF₁-fsn nu (trans (cofK n [] y ys) (cong (cofA []) c)) m)
```

`liLabK` (节点层 0, 链原子在第 0 层): `liLabᴸ` 逐字. 原子的自相似由 `ψK-≅ (suc n)`, 原子的证书与标签由递归 `rec` 在目标证明 `σ q` 处给出.

```agda
liLabK : ∀ n {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} {P : Vec (Frame L) (suc n)} {q : zero <ᴵ k} {f : Uˢ zero (<→◃ q) → Ordˢ k} {y ys} →
         AΩ P → cof (y ∷ ys) ≡ cΩ [] → Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → NF₁ (ctxK n (y ∷ ys)) →
         (rec : ∀ (p′ : zero <ᴵ L) θ (x : Ordˢ zero) → Atomᴸ x θ → f (intoˢ (<→◃ q) x) ≅ˢ f (intoˢ (<→◃ q) x) →
                NF₁ (ctxK n (fsT (y ∷ ys) θ)) →
                Σ (Goodᴸ (toZ (ψᴾ (suc n) p′ σ P (f (intoˢ (<→◃ q) x))))) λ G → Lab (forceᴸ _ G) (ctxK n (fsT (y ∷ ys) θ))) →
         Σ (Goodᴸ (toZ (ψᴾ (suc n) p σ P (Ord₊ˢ.limᵢ q f)))) λ G → Lab (forceᴸ _ G) (ctxK n (y ∷ ys))
liLabK n {p = p} {σ = σ} {P = P} {q = q} {f = f} {y = y} {ys = ys} A c ex nu rec =
  subst (λ W → Σ (Goodᴸ (toZ W)) λ G → Lab (forceᴸ _ G) (ctxK n (y ∷ ys))) (sym eqf)
        (limᴸ nu (cofωK n c) (λ m → proj₁ (outp m))
              (λ m → subst (Lab _) (sym (gtK n [] y ys [] c refl m)) (proj₂ (outp m))))
  where
  eqf = fold1K {p = p} {σ = σ} {P = P} {q = q} {f = f} (inj₂ z≅)
  atm : ∀ m → Atomᴸ (chainK σ P q f m) (γK n (y ∷ ys) [] m)
  atm zero    = Ωˢ-refl zero , gs gz , l1 refl (s≅ z≅) (l0 refl z≅)
  atm (suc m) = ψK-≅ (suc n) {p = σ q} {σ = σ} {p′ = σ q} {σ′ = σ} A A z≅ (i-respˢ ex (proj₁ (atm m))) ,
                rec (σ q) _ _ (atm m) (i-respˢ ex (proj₁ (atm m))) (nfγK n nu c m)
  outp : ∀ m → Σ (Goodᴸ (toZ (ψᴾ (suc n) p σ P (f (intoˢ (<→◃ q) (chainK σ P q f m)))))) λ G →
              Lab (forceᴸ _ G) (ctxK n (fsT (y ∷ ys) (γK n (y ∷ ys) [] m)))
  outp m = rec p _ _ (atm m) (i-respˢ ex (proj₁ (atm m))) (nfγK n nu c m)
```

`foldLabK` (节点层非零): 链点由 §3 的 `PreK₊ n` 标.

```agda
foldLabK : ∀ n {L k j y ys v vs} {p : zero <ᴵ L} {σ : Simᴵ k L} {P : Vec (Frame L) (suc n)} {q : j <ᴵ k}
           {f : Uˢ j (<→◃ q) → Ordˢ k} → AΩ P →
           cof (y ∷ ys) ≡ cΩ (v ∷ vs) → (I : Idx (v ∷ vs)) → j ≅ᴵ lvI I → kd j ≡ false →
           Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → NF₁ (ctxK n (y ∷ ys)) →
           (h : ∀ η (x : Ordˢ j) → LabL x η → LabL₊ k Ll (f (intoˢ (<→◃ q) x)) (fsT (y ∷ ys) η)) →
           (rec : ∀ η (x : Ordˢ j) → LabL x η → f (intoˢ (<→◃ q) x) ≅ˢ f (intoˢ (<→◃ q) x) →
                  NF₁ (ctxK n (fsT (y ∷ ys) η)) →
                  Σ (Goodᴸ (toZ (ψᴾ (suc n) p σ P (f (intoˢ (<→◃ q) x))))) λ G → Lab (forceᴸ _ G) (ctxK n (fsT (y ∷ ys) η))) →
           Σ (Goodᴸ (toZ (ψᴾ (suc n) p σ P (Ord₊ˢ.limᵢ q f)))) λ G → Lab (forceᴸ _ G) (ctxK n (y ∷ ys))
foldLabK n {y = y} {ys = ys} {v = v} {vs = vs} {p = p} {σ = σ} {P = P} {q = q} {f = f} A c I ej kj ex nu h rec =
  subst (λ W → Σ (Goodᴸ (toZ W)) λ G → Lab (forceᴸ _ G) (ctxK n (y ∷ ys))) (sym eqf)
        (limᴸ nu cω′ (λ m → proj₁ (outp m))
              (λ m → subst (Lab _) (sym (gtK n [] y ys (v ∷ vs) c refl m)) (proj₂ (outp m))))
  where
  cω′ : cof (ctxK n (y ∷ ys)) ≡ cω
  cω′ = trans (cofK n [] y ys) (cong (cofA []) c)
  eqf = fold1K {p = p} {σ = σ} {P = P} {q = q} {f = f} (inj₁ (z≺I I ej (λ ())))
  chainL : ∀ m → LabL (chainK σ P q f m) (γK n (y ∷ ys) (v ∷ vs) m)
  chainL zero    = LabL-Ω (proj₁ I) (proj₁ (proj₂ I)) (proj₁ (proj₂ (proj₂ I))) (proj₂ (proj₂ (proj₂ I))) ej
  chainL (suc m) = frL₊ kj (PreK₊ n {p = σ q} {σ = σ} {P = P} A I ej kj (h _ _ (chainL m)))
  nf : ∀ m → NF₁ (ctxK n (fsT (y ∷ ys) (γK n (y ∷ ys) (v ∷ vs) m)))
  nf m = subst NF₁ (gtK n [] y ys (v ∷ vs) c refl m) (NF₁-fsn nu cω′ m)
  outp : ∀ m → Σ (Goodᴸ (toZ (ψᴾ (suc n) p σ P (f (intoˢ (<→◃ q) (chainK σ P q f m)))))) λ G →
              Lab (forceᴸ _ G) (ctxK n (fsT (y ∷ ys) (γK n (y ∷ ys) (v ∷ vs) m)))
  outp m = rec _ _ (chainL m) (i-respˢ ex (chainK-≅ A ex m)) (nf m)
```

`ŝChainK` (非零层闭包 `gŝ` 在 $\psi_0$ 前缀下成为待计值链): `ŝChainᴸ` 逐字. 支配仍是 GoodLBase 的 `domᴸ`: 链点标签 `ctxK n b` 字面就是 `ctx (ΠΩ n b)`, 闭包地板 $w$ 出现在 $b$ 里 (`ow`), 往外包 $n$ 层 (`OccΠ n`), 于是 `domᴸ` 不改一字地适用 (它对 `ctx` 的参数没有形状要求).

```agda
ŝChainK : ∀ n {L k c w} {p : zero <ᴵ L} {σ : Simᴵ k L} {P : Vec (Frame L) (suc n)} {t₀ : Ordˢ k}
          {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} {y ys} →
          cof (y ∷ ys) ≡ cΩ [] → NF₁ (ctxK n (y ∷ ys)) → (Iw : Idx w) → c ⊑ᴵ suc (lvI Iw) → (∀ θ → Occ w (fsT (y ∷ ys) θ)) →
          (rec₀ : Σ (Goodᴸ (toZ (ψᴾ (suc n) p σ P t₀))) λ G → Lab (forceᴸ _ G) (γK n (y ∷ ys) [] 1)) →
          (rec : ∀ m Y (hY : HS Y) → Lab Y (γK n (y ∷ ys) [] (suc m)) → (e : c ⊑ᴵ toLevel Y hY) →
                 Σ (Goodᴸ (toZ (ψᴾ (suc n) p σ P (g (toLevel Y hY) e)))) λ G → Lab (forceᴸ _ G) (γK n (y ∷ ys) [] (suc (suc m)))) →
          Σ (Goodᴸ (ĉᴸ c (toZ (ψᴾ (suc n) p σ P t₀)) (λ η e → toZ (ψᴾ (suc n) p σ P (g η e)))
                         (toZ (ψᴾ (suc n) p σ P t₀)) (λ η e → toZ (ψᴾ (suc n) p σ P (g η e))))) λ G →
            Lab (forceᴸ _ G) (ctxK n (y ∷ ys))
ŝChainK n {y = y} {ys = ys} c nu Iw bw ow rec₀ rec =
  ĉᴸ-mk nu (cofωK n c) K (proj₁ rec₀) (subst (Lab _) (sym (gtK n [] y ys [] c refl 0)) (proj₂ rec₀))
        (λ k → CCᴸ.Gg K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
        (λ k → subst (Lab _) (sym (gtK n [] y ys [] c refl (suc k)))
                     (CCᴸ.lE K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k))))
  where
  K = ccᴸ (λ m → γK n (y ∷ ys) [] (suc m)) (proj₁ rec₀) (proj₂ rec₀)
          (domᴸ _ Iw bw (OccΠ n (ow (natT 1))) (proj₂ rec₀) (nfγK n nu c 0))
          (λ m Y hY lY e → proj₁ (rec m Y hY lY e)) (λ m Y hY lY e → proj₂ (rec m Y hY lY e))
          (λ m Y hY lY e → domᴸ _ Iw bw (OccΠ n (ow (γK n (y ∷ ys) [] (suc m)))) (proj₂ (rec m Y hY lY e)) (nfγK n nu c (suc m)))
```

**弹栈 `pop0K`, 唯一用到帧数的地方 (目标 $0$).** $n=0$: GoodLBase 的 `pop0ᴸ` (标签 $\psi_0(\Omega_\Omega)$ = `ctxK 0 []`). $n=m+1$: 经 `pop-eq`, 闭包 `ŝ (suc zero) t₀ g` 在第 0 层就是待计值链. 链证书 `K`: 标签序列 `δ m`, 第 0 点 `R₀` 与分支 `Rg` 都是**递归** `Pre0VK m` ($m+1$ 帧, 尾巴 $\Omega_1$ 与 $\Omega_{\mathtt{lvl}\,Y}$), 支配 $1\sqsubseteq^\mathsf I$ 由 `one⊑lab` (标签非零; 这里界是 $1$, 不需要 `domᴸ`), 输出就是链点, 单调由 `ĉᴸ-mk` (`mono-lab`, 即 `Lab-oc` + `fs-mono₁` 于 $\psi_0(\Omega_\Omega\cdot(m+2))$). 这正是 GoodL 的 `K2`/`GL2` 抬高 $m$ 帧: GoodL 里 $t_2$ 的链点由单帧 `Pre0Vᴸ` 标, 这里由 $m+1$ 帧的 `Pre0VK m` 标.

```agda
pop0K  : ∀ n {L k} (p : zero <ᴵ L) (σ : Simᴵ k L) {P : Vec (Frame L) (suc n)} → AΩ P →
         Σ (Goodᴸ (toZ (ψᴾ (suc n) p σ P Ord₊ˢ.zero))) λ G → Lab (forceᴸ _ G) (ctxK n [])
Pre0AK : ∀ n {L} {p : zero <ᴵ L} {σ : Simᴵ zero L} {P : Vec (Frame L) (suc n)} {x : Ordˢ zero} {a} → AΩ P →
         Lab0ᴸ x a → x ≅ˢ x → NF₁ (ctxK n a) → Σ (Goodᴸ (toZ (ψᴾ (suc n) p σ P x))) λ G → Lab (forceᴸ _ G) (ctxK n a)
Pre0VK : ∀ n {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} {P : Vec (Frame L) (suc n)} {x : Ordˢ k} {a} → AΩ P →
         LabL x a → x ≅ˢ x → NF₁ (ctxK n a) → Σ (Goodᴸ (toZ (ψᴾ (suc n) p σ P x))) λ G → Lab (forceᴸ _ G) (ctxK n a)
Pre0K₊ : ∀ n {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} {P : Vec (Frame L) (suc n)} {x : Ordˢ k} {a} → AΩ P →
         LabL₊ k Ll x a → x ≅ˢ x → NF₁ (ctxK n a) → Σ (Goodᴸ (toZ (ψᴾ (suc n) p σ P x))) λ G → Lab (forceᴸ _ G) (ctxK n a)

pop0K zero p σ (a∷ {z = z} aε) = pop0ᴸ p σ z
pop0K (suc n) p σ (a∷ {z = z} {P = P₁} A₁) =
  subst (λ W → Σ (Goodᴸ (toZ W)) λ G → Lab (forceᴸ _ G) (ctxK (suc n) [])) (sym (pop-eq {p = p} {σ = σ} {z = z} {P = P₁} A₁))
        (ĉᴸ-mk (ctxK-NF (suc n)) (cof-pop0 n) K (proj₁ R₀) (subst (Lab _) (sym (fs-pop0 n 0)) (proj₂ R₀))
               (λ k → CCᴸ.Gg K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
               (λ k → subst (Lab _) (sym (fs-pop0 n (suc k)))
                            (CCᴸ.lE K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))))
  where
  o = z<suc z p
  nfδ : ∀ j → NF₁ (δ n j)
  nfδ j = subst NF₁ (fs-pop0 n j) (NF₁-fsn (ctxK-NF (suc n)) (cof-pop0 n) j)
  R₀ : Σ (Goodᴸ (toZ (ψᴾ (suc n) zero (σ1 o) (replicateV (suc n) (fΩ̂ o)) (Ωˢ (suc zero))))) λ G → Lab (forceᴸ _ G) (δ n 0)
  R₀ = Pre0VK n {p = zero} {σ = σ1 o} {P = replicateV (suc n) (fΩ̂ o)} (AΩ-rep (suc n))
              (LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _)) (Ωˢ-refl (suc zero)) (nfδ 0)
  Rg : ∀ j Y (hY : HS Y) → Lab Y (δ n j) → (e : suc zero ⊑ᴵ toLevel Y hY) →
       Σ (Goodᴸ (toZ (ψᴾ (suc n) {ℓ = Mlev (suc zero) (toLevel Y hY) e} (lim 0 zero) (λ q → lim 1 q)
                          (liftV (λ q → lim 0 q) (replicateV (suc n) (fΩ̂ o))) (Ωˢ (toLevel Y hY))))) λ G →
         Lab (forceᴸ _ G) (δ n (suc j))
  Rg j Y hY lY e = Pre0VK n {p = lim 0 zero} {σ = λ q → lim 1 q} {P = liftV (λ q → lim 0 q) (replicateV (suc n) (fΩ̂ o))}
                          (AΩ-lift (AΩ-rep (suc n))) (LabL-Ω Y hY lY (nfδ j) (≅ᴵ-refl _)) (Ωˢ-refl _) (nfδ (suc j))
  K = ccᴸ (δ n) (proj₁ R₀) (proj₂ R₀) (one⊑lab _ (proj₂ R₀) (nfδ 0) []<)
          (λ j Y hY lY e → proj₁ (Rg j Y hY lY e)) (λ j Y hY lY e → proj₂ (Rg j Y hY lY e))
          (λ j Y hY lY e → one⊑lab _ (proj₂ (Rg j Y hY lY e)) (nfδ (suc j)) []<)
```

`Pre0AK` (尾巴在第 0 层, 对原子的 `Lab0ᴸ`): `Pre0ᴸ` 逐字, `lz` 改调 `pop0K n`.

```agda
Pre0AK n {p = p} {σ = σ} {a = []} A (lz c) ex nu = pop0K n p σ A
Pre0AK n {a = y ∷ ys} A (lz c) ex nu = ⊥-elim (cof-ne y ys c)
Pre0AK n {a = []} A (ls () l) ex nu
Pre0AK n {p = p} {σ = σ} {P = P} {a = y ∷ ys} A (ls c l) ex nu =
  limᴸ nu cω′ (λ m → proj₁ (Rs m)) (λ m → subst (Lab _) (sym (repK n [] y ys c m)) (proj₂ (Rs m)))
  where
  cω′ = trans (cofK n [] y ys) (cong (cofA []) c)
  Rp = Pre0AK n {p = p} {σ = σ} {P = P} A l (s-invˢ ex) (subst NF₁ (repK n [] y ys c 1) (NF₁-fsn nu cω′ 1))
  Rs = repᴸ (proj₁ Rp) (proj₂ Rp) (λ m → subst NF₁ (repK n [] y ys c m) (NF₁-fsn nu cω′ m))
Pre0AK n {a = []} A (ll () h) ex nu
Pre0AK n {p = p} {σ = σ} {P = P} {a = y ∷ ys} A (ll c h) ex nu =
  limᴸ nu (trans (cofK n [] y ys) (cong (cofA []) c))
       (λ m → proj₁ (Pre0AK n {p = p} {σ = σ} {P = P} A (h m) (l-invˢ ex m) (nfωK n nu c m)))
       (λ m → subst (Lab _) (sym (ωK n [] y ys c m)) (proj₂ (Pre0AK n {p = p} {σ = σ} {P = P} A (h m) (l-invˢ ex m) (nfωK n nu c m))))
Pre0AK n {a = []} A (lŝ₀ () K h₀ hk) ex nu
Pre0AK n {p = p} {σ = σ} {P = P} {a = y ∷ ys} A (lŝ₀ c K h₀ hk) ex nu =
  ĉᴸ-mk nu (trans (cofK n [] y ys) (cong (cofA []) c)) K (proj₁ R₀) (subst (Lab _) (sym (ωK n [] y ys c 0)) (proj₂ R₀))
        (λ k → proj₁ (Rk k)) (λ k → subst (Lab _) (sym (ωK n [] y ys c (suc k))) (proj₂ (Rk k)))
  where
  R₀ = Pre0AK n {p = p} {σ = σ} {P = P} A h₀ (ŝ-refl₀ ex) (nfωK n nu c 0)
  Rk = λ k → Pre0AK n {p = p} {σ = σ} {P = P} A (hk k) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) (nfωK n nu c (suc k))
Pre0AK n {a = []} A (lĉ () K h₀ hk) ex nu
Pre0AK n {p = p} {σ = σ} {P = P} {a = y ∷ ys} A (lĉ c K h₀ hk) ex nu =
  ĉᴸ-mk nu (trans (cofK n [] y ys) (cong (cofA []) c)) K (proj₁ R₀) (subst (Lab _) (sym (ωK n [] y ys c 0)) (proj₂ R₀))
        (λ k → proj₁ (Rk k)) (λ k → subst (Lab _) (sym (ωK n [] y ys c (suc k))) (proj₂ (Rk k)))
  where
  R₀ = Pre0AK n {p = p} {σ = σ} {P = P} A h₀ (ĉ-refl₀ ex) (nfωK n nu c 0)
  Rk = λ k → Pre0AK n {p = p} {σ = σ} {P = P} A (hk k) (ĉ-reflg ex _ _) (nfωK n nu c (suc k))
```

`Pre0VK`/`Pre0K₊`: `Pre0Vᴸ`/`Pre0L₊ᴸ` 逐字, `gz` 改调 `pop0K n`, 记号引理换成 $n$ 帧版.

```agda
Pre0VK n {k = zero}    {p = p} {σ = σ} {P = P} A at ex nu = Pre0AK n {p = p} {σ = σ} {P = P} A (atomL at) ex nu
Pre0VK n {k = suc _}   {p = p} {σ = σ} {P = P} A h  ex nu = Pre0K₊ n {p = p} {σ = σ} {P = P} A h ex nu
Pre0VK n {k = lim _ _} {p = p} {σ = σ} {P = P} A h  ex nu = Pre0K₊ n {p = p} {σ = σ} {P = P} A h ex nu

Pre0K₊ n {p = p} {σ = σ} {a = []} A (gz c) ex nu = pop0K n p σ A
Pre0K₊ n {a = y ∷ ys} A (gz c) ex nu = ⊥-elim (cof-ne y ys c)
Pre0K₊ n {a = []} A (gs () l) ex nu
Pre0K₊ n {p = p} {σ = σ} {P = P} {a = y ∷ ys} A (gs c l) ex nu =
  limᴸ nu cω′ (λ m → proj₁ (Rs m)) (λ m → subst (Lab _) (sym (repK n [] y ys c m)) (proj₂ (Rs m)))
  where
  cω′ = trans (cofK n [] y ys) (cong (cofA []) c)
  Rp = Pre0K₊ n {p = p} {σ = σ} {P = P} A l (s-invˢ ex) (subst NF₁ (repK n [] y ys c 1) (NF₁-fsn nu cω′ 1))
  Rs = repᴸ (proj₁ Rp) (proj₂ Rp) (λ m → subst NF₁ (repK n [] y ys c m) (NF₁-fsn nu cω′ m))
Pre0K₊ n {a = []} A (gl () h) ex nu
Pre0K₊ n {p = p} {σ = σ} {P = P} {a = y ∷ ys} A (gl c h) ex nu =
  limᴸ nu (trans (cofK n [] y ys) (cong (cofA []) c))
       (λ m → proj₁ (Pre0K₊ n {p = p} {σ = σ} {P = P} A (h m) (l-invˢ ex m) (nfωK n nu c m)))
       (λ m → subst (Lab _) (sym (ωK n [] y ys c m)) (proj₂ (Pre0K₊ n {p = p} {σ = σ} {P = P} A (h m) (l-invˢ ex m) (nfωK n nu c m))))
Pre0K₊ n {p = p} {σ = σ} {P = P} A (gu {r = zero} l) ex nu =
  Pre0VK n {p = p} {σ = λ q → σ (suc q)} {P = P} A l (u-reflˢ zero ex) nu
Pre0K₊ n {p = p} {σ = σ} {P = P} A (gu {r = self m} l) ex nu =
  Pre0VK n {p = p} {σ = λ q → σ (lim m q)} {P = P} A l (u-reflˢ (self m) ex) nu
Pre0K₊ n {a = []} A (gi () I ej h) ex nu
Pre0K₊ n {p = p} {σ = σ} {P = P} {a = y ∷ ys} A (gi {j = zero} {q = q} {f = f} c I ej h) ex nu =
  liLabK n {p = p} {σ = σ} {P = P} {q = q} {f = f} A (trans c (cong cΩ (kdI I (sym (kd-≅ ej))))) ex nu
         (λ p′ θ x at br nf → Pre0K₊ n {p = p′} {σ = σ} {P = P} A (h θ x (→Ll (<→◃ q) at)) br nf)
Pre0K₊ n {a = y ∷ ys} A (gi {ν = []} {j = suc _} c I ej h) ex nu = ⊥-elim (tf (trans (sym (kdI[] I)) (sym (kd-≅ ej))))
Pre0K₊ n {p = p} {σ = σ} {P = P} {a = y ∷ ys} A (gi {ν = v ∷ vs} {j = suc _} {q = q} {f = f} c I ej h) ex nu =
  foldLabK n {p = p} {σ = σ} {P = P} {q = q} {f = f} A c I ej refl ex nu (λ η x l → h η x (→Ll (<→◃ q) l))
           (λ η x l br nf → Pre0K₊ n {p = p} {σ = σ} {P = P} A (h η x (→Ll (<→◃ q) l)) br nf)
Pre0K₊ n {a = y ∷ ys} A (gi {ν = []} {j = lim _ _} c I ej h) ex nu = ⊥-elim (tf (trans (sym (kdI[] I)) (sym (kd-≅ ej))))
Pre0K₊ n {p = p} {σ = σ} {P = P} {a = y ∷ ys} A (gi {ν = v ∷ vs} {j = lim _ _} {q = q} {f = f} c I ej h) ex nu =
  foldLabK n {p = p} {σ = σ} {P = P} {q = q} {f = f} A c I ej refl ex nu (λ η x l → h η x (→Ll (<→◃ q) l))
           (λ η x l br nf → Pre0K₊ n {p = p} {σ = σ} {P = P} A (h η x (→Ll (<→◃ q) l)) br nf)
Pre0K₊ n {k = zero} A (gŝ () c Iw bw ow h₀ hg) ex nu
Pre0K₊ n {k = suc _} {a = []} A (gŝ kk () Iw bw ow h₀ hg) ex nu
Pre0K₊ n {k = suc _} {p = p} {σ = σ} {P = P} {a = y ∷ ys} A (gŝ kk c Iw bw ow h₀ hg) ex nu =
  ŝChainK n {p = p} {σ = σ} {P = P} c nu Iw bw ow
          (Pre0K₊ n {p = p} {σ = σ} {P = P} A h₀ (ŝ-refl₀ ex) (nfγK n nu c 0))
          (λ m Y hY lY e → Pre0K₊ n {p = p} {σ = σ} {P = P} A (hg _ Y hY lY (nfγK n nu c m) (1<ctx _) e)
                                   (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) (nfγK n nu c (suc m)))
Pre0K₊ n {k = lim _ _} {a = []} A (gŝ kk () Iw bw ow h₀ hg) ex nu
Pre0K₊ n {k = lim _ _} {p = p} {σ = σ} {P = P} {a = y ∷ ys} A (gŝ kk c Iw bw ow h₀ hg) ex nu =
  ŝChainK n {p = p} {σ = σ} {P = P} c nu Iw bw ow
          (Pre0K₊ n {p = p} {σ = σ} {P = P} A h₀ (ŝ-refl₀ ex) (nfγK n nu c 0))
          (λ m Y hY lY e → Pre0K₊ n {p = p} {σ = σ} {P = P} A (hg _ Y hY lY (nfγK n nu c m) (1<ctx _) e)
                                   (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) (nfγK n nu c (suc m)))
Pre0K₊ n {a = []} A (gĉ () K h₀ hk) ex nu
Pre0K₊ n {p = p} {σ = σ} {P = P} {a = y ∷ ys} A (gĉ c K h₀ hk) ex nu =
  ĉᴸ-mk nu (trans (cofK n [] y ys) (cong (cofA []) c)) K (proj₁ R₀) (subst (Lab _) (sym (ωK n [] y ys c 0)) (proj₂ R₀))
        (λ k → proj₁ (Rk k)) (λ k → subst (Lab _) (sym (ωK n [] y ys c (suc k))) (proj₂ (Rk k)))
  where
  R₀ = Pre0K₊ n {p = p} {σ = σ} {P = P} A h₀ (ĉ-refl₀ ex) (nfωK n nu c 0)
  Rk = λ k → Pre0K₊ n {p = p} {σ = σ} {P = P} A (hk k) (ĉ-reflg ex _ _) (nfωK n nu c (suc k))
```

**读法.** 停机一次通过, 包括 `pop0K (suc m)` 的 `where` 块里对 `Pre0VK m` 的调用 (帧数严格下降; DecoupleBase 记下的 "`where` 里的链体" 问题出在帧数不变的调用上, 这里不出现). 互递归 `pop0K (suc m) → Pre0VK m → Pre0K₊ m → {pop0K m, liLabK, foldLabK → PreK₊ m, ŝChainK}`.

## §5 哪些引理需要帧数, 怎么用

| 引理 (单帧原名) | $n$ 帧版 | 是否用到帧数 | 怎么改 |
|---|---|---|---|
| `popL` | `popLK` | **是** | $n=0$ 调原 `popL`; $n=m+1$: `pop-eq` 改写后造 `gŝ`, 第 0 点与分支递归 `PreVK m`, 记号 `fsT-popw`/`cof-popw`; 地板、界、`oh` 不变 |
| `pop0ᴸ` | `pop0K` | **是** | $n=0$ 调原 `pop0ᴸ`; $n=m+1$: 链证书 `K` 的点由递归 `Pre0VK m`, 支配 `one⊑lab`, 记号 `fs-pop0`/`δ` |
| `ψ1-≅` | `ψK-≅` (+ `liK`) | **是** | 弹栈子句递归到 $n$ 帧 (两个不同的 `AΩ` 栈); `lᵢ≅` 子句须拆出 `liK` 才过停机 |
| `ψᴾ` 的 `rebase` | `pop-eq` | **是** (读栈内容) | `AΩ P → onlyΩ̂ P ≡ true`, `rewrite` |
| `giPreL`, `PreAL`/`PreVL`/`PreL₊` | `giPreK`, `PreAK`/`PreVK`/`PreK₊` | 否 (只带着) | 记号前缀 `ΩΩ ∷ b` → `ΠΩ (suc n) b`; `od (ot o)` → `od (OccΠ (suc n) o)` |
| `liLabᴸ`, `foldLabᴸ`, `ŝChainᴸ` | `liLabK`, `foldLabK`, `ŝChainK` | 否 | 同上; `ŝChainK` 的 `domᴸ` 用 `OccΠ n` |
| `Pre0ᴸ`, `Pre0Vᴸ`/`Pre0L₊ᴸ` | `Pre0AK`, `Pre0VK`/`Pre0K₊` | 否 | 同上 |
| `chain1`/`fold1`/`pen1` | `chainK`/`fold1K`/`pen1K` | 否 | 任意栈 |
| `ctx`/`ctxw`, `γP`, `nfγ`/`nfω` | `ctxK`/`ctxwK`, `γK`, `nfγK`/`nfωK` | 是 (记号参数) | `ctxK n a = ctx (ΠΩ n a)`; 交换引理 `cofΠ`/`predΠ`/`fsnΠ`/`fsTΠ` |
| `Goodᴸ`, `gc`, `forceᴸ`, `limᴸ`, `ĉᴸ-mk`, `domᴸ`, `fs-mono₁`, `mono-lab`, `LabL` (含 `gŝ` 地板), `LabL-Ω`, `LSum₊`/`LRep`, `PsiVL`, `atomL`, `repᴸ` | 原样导入 | 否 | 不改 |

## §6 结论与边界

**字面成立 (`refl`):** `ctxK n a ≡ ψ₀(ΠΩ (suc n) a)`, `ctxK 0 ≡ ctx`; `walk tO (1 ∷ []) ≡ tΩ2`, `walk tO (1 ∷ 0 ∷ 0 ∷ []) ≡ tω`; `fsn (tk 3) 0/1/2`, `fsn tω 0 ≡ 1`, `fsn tω 3 ≡ tk 3`, `fsn tΩ2 0/1`, `walk tΩ2 [0,0] ≡ tω`, `walk tΩ2 [0,1] ≡ ψ₀(ψ_Ω(tω))`, `walk tΩ2 [0,1,1] ≡ ψ₀(ψ_Ω(tk 1))`; 对每个具体的 $n$, `pop-eq` 化为 `refl`.

**定理 (对一切 $n$):**

1. 记号: `cofΠ`/`predΠ`/`fsnΠ`/`fsTΠ`/`cofΠ0`/`fsTΠ0`/`OccΠ`/`ΠΩ-rep`; `repK`/`ωK`/`γK-eq`/`gtK`/`penK`/`H1K`; `fs-pop0`, `cof-pop0`, `fsT-popw`, `cof-popw`; **`fs-tω : fsn tω k ≡ tk k`**; **`tk-NF`, `tω-NF`, `tΩ2-NF`**, `ctxK-NF`.
2. 栈: `AΩ`, `onlyA`, `AΩ-rep`, `AΩ-lift`, **`pop-eq`**; **`ψK-≅`** (+ `liK`), `chainK-≅`, `fold1K`, `pen1K`.
3. 目标 $w\ne0$: **`popLK`, `giPreK`, `PreAK`/`PreVK`/`PreK₊`**.
4. 目标 $0$, 证书与标签一起: `cofωK`, `nfγK`, `nfωK`, `liLabK`, `foldLabK`, `ŝChainK`, **`pop0K`, `Pre0AK`/`Pre0VK`/`Pre0K₊`**: 对尾巴的 `LabL` 推导, $n+1$ 帧 $\psi_0$ 的计值树的 `Goodᴸ` 证书与标签 $\psi_0(\Omega_\Omega\cdot(n+1)+a)$ 同时存在 (任意环境层号、`Sim`、帧证据).

**边界.**

- 只处理纯 $\hat\Omega$ 栈 (`AΩ`); `fT` 帧与 Prefix 的非紧界 (`rebase′ false`) 不在本文范围.
- 对抽象 $n$, `ψᴾ (suc n) … zero` 与 `popˢ n …` 只命题相等 (`pop-eq`), 所以 $n$ 帧树的外层形状对抽象 $n$ 只经 `subst`; 对具体 $n$ 一切都化简 (OmegaK §1 的 `T3ᴸ ≡ lim χ3`).
- $\psi_\Omega(\eta)$ ($\eta\ne0$) 的帧不存在, 见 OmegaK §4.
