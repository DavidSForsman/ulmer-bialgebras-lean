# Build the Lean documentation

This separate Lake package pins doc-gen4 to the Lean release used by the project. From this
folder, run:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
lake build +Companion.Statements:docs +Companion.Proofs:docs
python3 -m http.server --directory .lake/build/doc
```

The generated pages are in `.lake/build/doc`. The current doc-gen4 facet also processes the
transitive imports, including Mathlib; allow space and time for those dependencies. To generate
paper declaration links to a published copy, run the development repository's `paper_links.py --docs-url URL`, where
`URL` is the base URL of the generated pages.
