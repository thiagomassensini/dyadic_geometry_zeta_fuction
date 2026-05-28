# Paper Draft

The canonical paper draft is:

```text
paper/main.tex
```

The review-facing companion files are:

```text
paper/THEOREM_MAP.md
paper/FORMALIZATION_COMPANION.md
```

For peer-review preparation, edit `main.tex` first and keep its Lean names
aligned with:

```text
paper/THEOREM_MAP.md
paper/FORMALIZATION_COMPANION.md
docs/MAIN_ROUTE_MAP.md
docs/THEOREM_MAP_REVIEW.md
docs/BOUNDS_CERTIFICATES_WITNESSES.md
docs/LEAN_MODULE_LAYOUT.md
```

Other Markdown files in this directory are historical working notes and
outlines unless explicitly promoted into the review-facing map above.

Suggested local build command:

```bash
cd paper
pdflatex main.tex
```
