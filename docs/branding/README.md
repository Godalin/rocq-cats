# Rocq-Cats reference tracing

# Rocq-Cats 参考图描摹

[SVG source](./rocq-cats.svg) · [Preview](./rocq-cats-preview.png)

[SVG 源文件](./rocq-cats.svg) · [预览](./rocq-cats-preview.png)

The supplied 1536 × 768 reference image determines the composition and
outlines. A large reclining cat encloses two resting medium cats and a
leaping kitten, with two motion marks. The reference's proportions, poses,
facial details, curled tails and varying contour widths are preserved.
Below the artwork, a centered signature places the official Rocq icon beside
the outlined wordmark “Rocq-Cats”. The full canvas is 1536 × 1024.

构图与轮廓以用户提供的 1536 × 768 参考图为准。横卧大猫包裹两只趴卧中猫、跃起
的小猫及两道运动线，保留原图的比例、姿态、表情细节、卷尾和轮廓粗细变化。
图案下方居中排列 Rocq 官方图标与轮廓字标“Rocq-Cats”，完整画布为 1536 × 1024。

The SVG contains closed cubic Bézier paths grouped as `large-cat`,
`upper-cat`, `lower-cat`, `running-kitten` and `motion-lines`. A shared smooth
purple gradient colors the paths; `background` is a removable white rectangle.
The artwork is self-contained, with no embedded bitmap, font dependency,
script or external resource. The PNG is a preview of the SVG.

SVG 使用闭合三次贝塞尔路径，按 `large-cat`、`upper-cat`、`lower-cat`、
`running-kitten` 和 `motion-lines` 分组。路径共享平滑紫色渐变，`background`
是可移除的白色矩形。图稿自包含，不嵌入位图，不依赖字体、脚本或外部资源。
PNG 是 SVG 的渲染预览。底部标识分别位于 `signature` 中的 `rocq-icon` 与
`wordmark` 分组，字标也已转成路径。

Tracing fits the sampled contours with a 0.24-source-pixel tolerance.
A temporary raster-mask comparison measured approximately 99.4 percent
intersection over union. The vector artwork retains the shapes rather than
the original image's paper grain and pixel noise; its smooth purple shading
approximates the reference. Adding the signature leaves all five cat-artwork
groups unchanged.

描摹以 0.24 个原图像素的容差拟合采样轮廓。临时栅格轮廓比较的交并比约为 99.4%。
矢量图保留形状，去除原图的纸面颗粒与像素噪声，并以平滑紫色渐变接近原图色彩。
添加底部标识时，猫图案的五个分组均保持原样。

Validation includes XML syntax, named groups, local paint references,
absence of raster content, contour comparison and inspection of the full
rendered preview. The tracing and comparison helpers are temporary checks,
not additional tools or permanent tests in the library.

已检查 XML 语法、分组、内部填色引用、位图缺失、轮廓比较及完整渲染预览。
描摹和比较辅助程序仅为临时检查，不向理论库加入额外工具或永久测试。

The Rocq icon uses the original outline from the official
[icon SVG](https://github.com/rocq-prover/rocq-prover.org/blob/dc102d304f370d6ec9d58e311c1465fbdf67c2df/rocq-id/logos/SVG/icon-rocq-black.svg),
recolored purple. The upstream
[license](https://github.com/rocq-prover/rocq-prover.org/blob/dc102d304f370d6ec9d58e311c1465fbdf67c2df/LICENSE)
releases the Rocq logo under the UNLICENSE. The wordmark uses outlined
Instrument Rocq Bold, based on Instrument Sans; the upstream
[font notices](https://github.com/rocq-prover/rocq-prover.org/blob/dc102d304f370d6ec9d58e311c1465fbdf67c2df/LICENSE-3RD-PARTY)
identify it as SIL Open Font License, copyright 2022 The Instrument Sans.
No font binary is included.

Rocq 图标使用官方
[图标 SVG](https://github.com/rocq-prover/rocq-prover.org/blob/dc102d304f370d6ec9d58e311c1465fbdf67c2df/rocq-id/logos/SVG/icon-rocq-black.svg)
的原始轮廓并改为紫色。上游
[许可证](https://github.com/rocq-prover/rocq-prover.org/blob/dc102d304f370d6ec9d58e311c1465fbdf67c2df/LICENSE)
将 Rocq 标志以 UNLICENSE 发布。字标使用 Instrument Rocq Bold 轮廓，其基础字体
为 Instrument Sans；上游
[字体声明](https://github.com/rocq-prover/rocq-prover.org/blob/dc102d304f370d6ec9d58e311c1465fbdf67c2df/LICENSE-3RD-PARTY)
将其标为 SIL Open Font License，版权为 2022 The Instrument Sans。本目录不包含
字体二进制文件。
