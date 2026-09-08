# U0/U1：规则对应表

状态：核心构造已落地，完整对象理论解释待证。

来源：[Setzer §4.3](https://csetzer.github.io/articles/mahlo.pdf)；现代外部形式对照 [Dybjer–Setzer §2](https://csetzer.github.io/articles/dybjerSetzerWeylVolume2025/dybjerSetzerWeylVolume2025Final.pdf)。表中“实现”只指所列宿主构造，不替代推导健全性定理。

| 规则／义务 | 对应实现 | 状态 |
|---|---|---|
| 大代码类型与解码 | `V = Set`，`T A = A` | 已实现候选 |
| 对每个族算子产生小宇宙 | `Close.U F`，`Close.El F` | 任意开放参数 F 下通过安全检查 |
| 小宇宙在大宇宙中的代码 | `u F`，`s F`，`u-decode` | 解码等式按定义成立 |
| 有限类型、自然数闭包 | `fin`、`nat` 及 El 方程 | 已实现 |
| 和、Π、Σ、W 闭包 | `sum`、`pi`、`sigma`、`w` | 已实现 |
| 同一类型内的等式闭包 | `eq`，解码到内建等式 | 已实现，不使用 K |
| Res0 的代码及解码 | `res₀` 及 El 方程 | 已实现 |
| Res1 的代码及解码 | `res₁` 及 El 方程 | 已实现，域依赖 Res0 的解码 |
| 族级限制映射 | `restrict` | 已实现 |
| 限制映射与大算子相容 | `commute` | 对所有 F 与小族成立 |
| §5.9 的指定族重编码 | `Recode.codeA/codeB` 及两条解码等式 | 已实现宿主实例 |
| 基础类型的全部对象消去规则 | 宿主原生构造提供候选 | 逐条翻译尚未完成 |
| 原论文全部判断等式、转换、代换 | 尚无完整对象推导语法 | 未完成 |
| 原良序证明需要的谓词／类的表示 | 尚无 distinguished sets 模块 | 未完成 |
| Lemma 5.10–5.11 | 尚无对应定理 | 未完成 |
| §5.14 的统一可达性证书 | 见 ENDPOINT.md | 未完成 |

## 不作为已证规则的事项

- 不为 V 添加按任意类型构造分析的消去器。
- 不采用本地旧 Op/Sub 骨架替代任意族算子。
- 不将“任意宿主 F 下构造成功”视为对象语法及全部规则保持已自动完成。
- 不要求任意函数之间可比较或函数外延性；相容等式来自具体解码方程。

## 复现

在仓库根目录运行：

```sh
agda --no-libraries -i src src/Mahlo/Universe/External.agda
```

模块显式启用 `--safe --without-K`，仅导入 Agda 内建模块。完整 src 验收另用 `tools/check-src.sh`。
