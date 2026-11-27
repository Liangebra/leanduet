# Language packs (schema 1)

LeanDuet separates mathematical proof structure from the language in which it is read or entered. Select a narrative language from the workbench toolbar, or import a UTF-8 JSON file (up to 256 KiB). Packs persist locally and never execute code. Built-in IDs `en`, `zh` and `ja` cannot be replaced. Community examples include [French](../examples/language-fr.json) and [Urdu](../examples/language-ur.json). Download the raw JSON file before importing it; each example is a sample, not a comprehensive translation.

## Import a community pack

1. Download the pack's raw `.json` file to your device.
2. Open the LeanDuet workbench and select the **Typed proof** view.
3. In the typed-proof tools, choose **Import language** and select the downloaded JSON file.
4. LeanDuet validates the file and, when it is accepted, adds the pack to the **Narrative language** selector. The imported pack is selected automatically.
5. The pack is saved in the current browser's local storage and remains available after reloading the workbench in that browser profile. Import it again on another browser or device.

The **Narrative language** preference controls mathematical proof explanations and supported controlled input. It is separate from **Interface language**, which changes the workbench controls and menus. Community packs do not translate the interface chrome.

## Schema

A pack has `schema: 1`, an `id` (lowercase ASCII, 2–24 characters), a human-readable `label`, `words`, `grammar`, `rules` and `aliases`.

The `words` table must contain these keys: `assume`, `introduce`, `witness`, `let`, `apply`, `obtain`, `use`, `opaque`, `function`, `edit`, `hidden` and `limited`. Use `{name}` for an identifier where appropriate.

The `rules` table maps exact Lean declaration names to readable mathematical phrases. Missing rules use the generic application phrase. The `aliases` table maps those declaration names to arrays of mathematical phrases that users can enter. Each alias should have one clear meaning. Conflicting aliases are rejected rather than guessed.

The `grammar` table must contain arrays named `prefix`, `using`, `join`, `establish`, `conclude` and `automatic`. These are literal tokens, not executable regular expressions. Keep the grammar small and use natural mathematical phrasing rather than word-for-word machine translation. English, Chinese, Japanese built-ins and installed community packs are accepted together by the controlled parser.

Rule availability is checked by Lean, not by the language pack. All rendering uses text nodes. Packs are data-only: never include scripts, HTML, regular expressions, remote resources or executable templates. Interface language (English, Chinese or Japanese) is a separate preference from mathematical narrative language.

Built-in exact-source examples have authored readings in all three interface languages. The Pages build also extracts their proof trees with the pinned Lean toolchain; those trees are read-only, shown only for byte-identical synchronized source, and do not constitute live verification. If the build-time data is absent, the static editor offers explicitly labelled authored readings instead.

Keep grammar small; arbitrary prose, inflection and ambiguous notation need future grammar backends. See Ranta, *Grammatical Framework* (JFP 2004) for the separation of abstract and concrete syntax. Contribute a JSON pack plus parser and rendering regression tests. A small, reviewed pack is more useful than a large unreviewed dictionary.
