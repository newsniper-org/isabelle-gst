# Preparing this development for the AFP

What an AFP entry is, measured against `~/afp` (upstream, 1012 entries) and
Isabelle2026-RC0, and where this development stands.

## What the AFP requires

An entry is a directory `thys/<Name>/` containing:

| | |
|---|---|
| `ROOT` | `chapter AFP` + one session named exactly `<Name>` |
| `document/root.tex` | the LaTeX driver; `\input{session}` pulls in the theories |
| `*.thy` | the theories, in that directory or its subdirectories |

and a `metadata/entries/<Name>.toml` in the AFP repository itself, carrying
`title`, `date`, `topics`, `abstract`, `license`, and an `[authors]` table
whose keys refer to `metadata/authors.toml`.

The session must build with `document=pdf`. That is the gate: a LaTeX error
is a failed entry, not a warning.

## Where this development stands

**Done.**

- `src/ROOT` declares one session with `document_files "root.tex"`, and every
  theory is reachable (2026-09-01: four theories no other theory imported were
  invisible to the build, and therefore had never been checked).
- `src/document/root.tex` is written in the AFP shape — title, author,
  abstract, `\tableofcontents`, `\input{session}`.
- **`isabelle build -o document=pdf` is green**: 238 pages, 0 LaTeX errors
  (2026-09-06). Getting there closed five defects, all of the same class — a
  document comment is TEXT, handed to LaTeX as written, and only an
  antiquotation goes through symbol translation:

  | | |
  |---|---|
  | `ModelKit/Tagging.thy` | uses `\<^enum>` as the mixfix of `Part`. That symbol is `group: document` (`etc/symbols`, code `0x25b8`) — meant for list markup inside comments, where the markup handler renders it and no macro is needed. Inside a TERM it goes out as `\isactrlenum`, which nothing defines: not in Isabelle's `lib/texinputs` (the only place `isabelle.sty` lives — the system TeX Live has no `isabelle*.sty` at all and `kpsewhich` returns nothing), not anywhere in the Isabelle2026-RC0 tree, and the local install's `.sty` files are byte-identical to the upstream tarball. `root.tex` now defines it with the glyph the symbol table assigns. **49 of the 78 errors.** |
  | `GZF/UPair.thy`, `Ordinal/Ordinal.thy` | bare `\<P>`, `\<emptyset>`, `\<omega>` in section titles reached LaTeX as literal `\<P>` — and hyperref repeated them in the PDF bookmark. Now `\<^term>` antiquotations. |
  | `GZF/SetComprehension.thy` | bare `\<lambda>` in a `text` block. |
  | `Founder/ZFC_in_HOL_Bootstrap.thy` | `ZFC_in_HOL` written as prose: `_` is math-mode-only in LaTeX. Now `\<^verbatim>`. |
  | `GZF/EmptySet.thy` | `&` in a section title — LaTeX's alignment tab, and again repeated into the bookmark. |

**Open, and NOT ours to decide.**

- **Authorship and license.** This is a port of Dunne and Wells's development;
  who submits it, under which AFP `license`, and which `[authors]` entries the
  metadata names are the copyright holders' calls, not ours.
- **Entry name.** `metadata/entries/<Name>.toml` and the session name must
  agree, and the name is what the entry is cited by.
- **Topics.** The AFP's topic list is fixed (`metadata/topics.toml`);
  "Logic/Set theory" is the obvious fit but the choice is the author's.

**Open, mechanical.**

- `chapter GST` becomes `chapter AFP` on submission.
- The entry directory is renamed to the entry name, since AFP takes
  `thys/<Name>/` rather than `src/`.
- `ZFC_in_HOL` is itself an AFP entry, so the dependency is already inside the
  AFP and needs no special handling.

## Reproducing the check

```
isabelle build -D src -c -o document=pdf GST
```

`-c` matters: without it a cached session reports success in four seconds
without running LaTeX at all.
