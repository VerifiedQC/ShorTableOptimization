#!/usr/bin/env bash
# Install the Lean toolchain named by ./lean-toolchain, and put elan on PATH
# for the rest of the job.
#
# Run from the root of a checkout, which is what every caller already does via
# `working-directory`. A composite action would be the usual way to share this,
# but `./.github/actions/...` resolves against the workspace root, and the
# promotion and submission workflows never check anything out there -- they
# check out into `source/`, `verifier/` and `submission/`. Sharing it as a file
# inside the checkout works in every caller and keeps the pin in one place.
#
# In the submission workflow the caller runs this from the trusted `verifier`
# checkout, never from the fork's tree.
set -euo pipefail

# Pinned so the installer cannot change underneath a job that pushes to `main`.
# 55dc281 is the current tip for this file; bump deliberately.
ELAN_INIT_REF=55dc2814ca42ace25f05ba4dd7a43a8c701a0549

curl -sSf "https://raw.githubusercontent.com/leanprover/elan/${ELAN_INIT_REF}/elan-init.sh" \
  | sh -s -- -y --default-toolchain "$(cat lean-toolchain)"
echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
