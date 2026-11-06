# External lecture images

The repository commits image-selection and access logic, source URLs, creators,
license records, and source revision identifiers. **It does not commit image
bytes.** [The portrait manifest](../dkvis/assets/history-images.yaml) is the
curated source list. Discovery and license review happen before adding an entry;
the downloader never searches for a replacement or silently chooses a new face.

Run commands below from `visualizations/`, using the project's Python environment
(`uv run python` in a normal installation).

## Fetch and use

```bash
uv run python -m dkvis.presentation.external_assets fetch
uv run python -m dkvis.presentation.external_assets status
```

The default store is `visualizations/asset-store/`, ignored as a whole. Each
image has a stable name such as `history/kahan.jpg` and a neighboring
`kahan.jpg.json` with its attribution/source snapshot, source revision, selected
rendition, checksum, fetch timestamp, size, and download duration. Keep those
files together. Already-cached images render without a network request. A
changed source record or damaged image is detected before use.

The original file or a standard Wikimedia thumbnail is retained unchanged;
slides scale proportionally and do not make a new crop. The larger photographs
use standard cached thumbnail sizes to reduce traffic and avoid requesting
arbitrary sizes. Existing crops on Commons are recorded in the source notes.
The source revision and the actual downloaded rendition are distinct records.

History deck preparation fetches missing entries. It stops with an error if an
image cannot be retrieved or its reviewed checksum no longer matches; it does
not produce a pretend portrait. A deliberate `fetch --refresh` re-downloads the
selected rendition. If Wikimedia has replaced that rendition, review the new
file and update the manifest before using it.

To keep the store elsewhere, configure an absolute directory:

```bash
export DKVIS_ASSET_DIR=/path/to/shared/lecture-assets
uv run python -m dkvis.presentation.external_assets fetch
make slides DECK=history-people-foundations
```

The CLI also accepts `--store /path/to/store` **before** its subcommand. The
renderer reads `DKVIS_ASSET_DIR`; the CLI-only override does not change later
render commands. An exported variable is sufficient; no private machine path
needs to be committed. This store is separate from disposable `media/` and
`renders/` outputs. Preserve it if you want offline rendering or to retain the
reviewed bytes should an upstream image change.

## Transfer a directory

Copy the complete store, including its JSON files, to the other machine:

```bash
rsync -av --progress asset-store/ other-host:/path/to/lecture-assets/
```

On the receiving machine, point `DKVIS_ASSET_DIR` there and run `status`.
Relative paths in metadata do not depend on the sender's home directory.

## Bundle for wormhole or IPFS

```bash
uv run python -m dkvis.presentation.external_assets bundle /tmp/dk-history-assets.tar.gz
# Transfer with the tool you prefer:
wormhole send /tmp/dk-history-assets.tar.gz
# Or, using your own IPFS node:
ipfs add /tmp/dk-history-assets.tar.gz
```

Those transfer commands are examples; the lecture builder does not contact a
remote recipient or publish to IPFS automatically. A bundle contains the
catalogued images and their source snapshots, not Git history, private `.env`
settings, renders, or unrelated local files. To bundle selected entries, append
their keys after the archive path. Bundle files are generated and stay out of Git.

After receiving a bundle with wormhole, or downloading a known CID with
`ipfs get <CID> -o /tmp/dk-history-assets.tar.gz`:

```bash
uv run python -m dkvis.presentation.external_assets import /tmp/dk-history-assets.tar.gz
uv run python -m dkvis.presentation.external_assets status
```

Import accepts regular catalogued image/metadata files only, detects conflicts,
and checks restored image integrity. It does not blindly extract arbitrary
archive paths. Matching copies are reusable. If an old and new image conflict,
import into a separate `--store` directory to inspect them rather than silently
replacing a reviewed source. Use the matching Git revision of the manifest
when restoring an older source selection.

## Attribution in the slides

Use `add_attributed_image` from `dkvis/components/attributed_image.py`. It places
the creator or credited collection, license name, source-page link, license
link, and display-change note beneath the image. People lectures also end in
readable source/license cards. Keep those credits when sharing a deck or video.
Creator names are not replaced by the model name on the lecture cover.

Public-domain status is distinguished from a Creative Commons grant. CC BY-SA
images retain their own license; the source rendition and credits can be shared
together from the bundle. Full file pages and license URLs stay in the committed
manifest and each local snapshot. Do not copy the Commons page's general text
license onto a photograph whose own file page says something else.
