# 探针与历史探索

**本目录不是成品区。** 这里保存中途探索、失败实验、局部可编译原型及研究报告。部分报告中的强度标签或不可能性判断尚未得到独立证明，亦可能被后续研究修正。默认文档构建不发布这些内容。

- [OCF](OCF/)：原 `src/OCF/` 中除 BTBO 之外的全部内容。旧的自然数指标迭代 [路线图](OCF/ROADMAP.md) 也保留在此。
- [Lens](Lens/)：原 `src/Lens/` 全部内容，包括预期编译失败的探针。
- 当前类型宇宙飞跃研究入口：[src/Mahlo](../src/Mahlo/README.md)。
- 成品 OCF 入口：[BTBO.lagda.md](../src/OCF/BTBO.lagda.md)。

## 检查方式

保留原 Agda 模块名，避免把目录归档变成数学实现修改。独立的 [probes.agda-lib](probes.agda-lib) 包含探针、成品源码和 Lens 的裸模块搜索路径；成品的主库不包含探针目录。

在仓库根目录、安装项目声明的依赖后，单独检查选定的 OCF 探针，例如：

```sh
agda probes/OCF/Higher.agda
```

Lens 只依赖 Agda 内建模块，可以避开项目库依赖单独检查：

```sh
agda --no-libraries -i probes/Lens probes/Lens/NoCubical.agda
agda --no-libraries -i probes/Lens probes/Lens/Probe4.agda
```

`Lens/Norm2.agda` 是预期失败的实验；不应以“整个探针目录全部编译通过”作为验收要求。旧记录中的版本与结果是当时的实测情况。
