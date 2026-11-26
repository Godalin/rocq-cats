# Rocq-Cats reference tracing

[SVG source](./rocq-cats.svg) · [Preview](./rocq-cats-preview.png)

The supplied 1536 × 768 reference image determines the composition and
outlines. A large reclining cat encloses two resting medium cats and a
leaping kitten, with two motion marks. The reference's proportions, poses,
facial details, curled tails and varying contour widths are preserved.
Below the artwork, a centered signature places the official Rocq icon beside
the outlined wordmark “Rocq-Cats”. The full canvas is 1536 × 1024.

The SVG contains closed cubic Bézier paths grouped as `large-cat`,
`upper-cat`, `lower-cat`, `running-kitten` and `motion-lines`. A shared smooth
purple gradient colors the paths; `background` is a removable white rectangle.
The artwork is self-contained, with no embedded bitmap, font dependency,
script or external resource. The PNG is a preview of the SVG.

Tracing fits the sampled contours with a 0.24-source-pixel tolerance.
A temporary raster-mask comparison measured approximately 99.4 percent
intersection over union. The vector artwork retains the shapes rather than
the original image's paper grain and pixel noise; its smooth purple shading
approximates the reference. Adding the signature leaves all five cat-artwork
groups unchanged.

Validation includes XML syntax, named groups, local paint references,
absence of raster content, contour comparison and inspection of the full
rendered preview. The tracing and comparison helpers are temporary checks,
not additional tools or permanent tests in the library.

The Rocq icon uses the original outline from the official
[icon SVG](https://github.com/rocq-prover/rocq-prover.org/blob/dc102d304f370d6ec9d58e311c1465fbdf67c2df/rocq-id/logos/SVG/icon-rocq-black.svg),
recolored purple. The upstream
[license](https://github.com/rocq-prover/rocq-prover.org/blob/dc102d304f370d6ec9d58e311c1465fbdf67c2df/LICENSE)
releases the Rocq logo under the UNLICENSE. The wordmark uses outlined
Instrument Rocq Bold, based on Instrument Sans; the upstream
[font notices](https://github.com/rocq-prover/rocq-prover.org/blob/dc102d304f370d6ec9d58e311c1465fbdf67c2df/LICENSE-3RD-PARTY)
identify it as SIL Open Font License, copyright 2022 The Instrument Sans.
No font binary is included.
