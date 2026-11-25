# KLp: 有限层上完全的层号定位器 (构造一路; 前缀 KLp, 工作目录 <实验目录>/m6p)

先读公共约束: <实验目录>/briefs/COMMON.md . 注意: 共享基目录是 <实验目录>/w8 (编译命令里的 `-i .../w4` 换成 `-i <实验目录>/w8`). w8 里都已编译, 只读: W4Block, W4Ops, W4Path, W4Fold, WVOne, WVTwo, KLoc.

## 背景

W4 的层号 `L` 自己是树 (W4Block: `zero`, `nd sS`, `nd sL`, `nd (sΩ k)`). 路径 `j ≤ a` (`Pth true j a`, 构造子 `self`, `inc`, `inu`, `ink`) 说的是层号 j 字面地出现在层号 a 里的某个位置. 第 0 层的树 z 读回成层号 `h₁ z = zero ⊕ ↑ zero z` (WVOne); 第 0 层的树只有 zero, suc, lim 三种, lim 带相邻项字面步进的证据 (`zero ⊢ f n ◃ f (suc n)`).
折叠朝 "某个孩子里的层 j" 折一棵 "在另一个孩子 c 里的树" 时, 现在一律回退 (丢信息). 若能在孩子 c 的层号里找到 j, 就可以在孩子 c 里就地折. 主审判断: j 是有限层 (`KLoc.lvl n`) 时, 定位可以做到完全, 不需要任何全知原理; 另一路在证 j 是无穷层时完全的定位推出 LPO.
接口在 <实验目录>/w8/KLoc.agda (已编译, 不要改): `Locator`, `lvl`, `CompleteFin`, `PosStmt`.

## 要交的

1. 一个定位器 `locF : Locator`, 对一般的层号对 (j, a) 都有定义 (认不出 j 是有限层, 或者在 a 里找不到时返回 nothing), 定义里不用任何证明作输入.
   - 认有限层: j 是不是一串 sS 结点接 zero; 认出后要一条命题相等 `j ≡ lvl n` (sS 的孩子类型是 ⊤, 有 η, 不需要函数外延).
   - 在 a 里找 `lvl n`: 对 a 结构递归. a 自己是有限层时按个数给路径; `nd sS h` 往孩子里找; `nd sL g` 只看有限个孩子 (建议看 g n 或 g (suc n)); `nd (sΩ _) _` 可以返回 nothing.
2. 证 `CompleteFin locF`: 对一切 n 与一切第 0 层的树 z, 只要 `lvl n ≤ h₁ z` 就找到. 证明里大概要一条引理: 合法的极限树 `lim f` 的第 n 项字面地在 sucⁿ zero 之上 (由相邻项的步进证据对 n 归纳), 以及 "字面地严格高于 sucⁿ zero 的树里有 suc^(n+1) zero" (对树结构归纳).
3. 导出 `pos : KLoc.PosStmt`.
4. 另给一条便于折叠使用的形式 (若顺手): `locZ : (n : ℕ) (z : Tr zero) → Maybe (lvl n ≤ h₁ z)` 及它与 `locF` 的关系.

## 要点

- 无前提: 不用函数外延, 不加公设.
- 若 `CompleteFin` 对你的 `locF` 证不出, 报出反例或卡住的确切位置 (例如某种合法的树里有限层的出现位置不在你看的那几个孩子里); 可以改搜索的孩子, 但搜索必须是有限的、对 a 结构递归的.
- 卡住时把没证的部分写成带确切陈述的模块参数, 使文件整体编译, 回报里列出.
