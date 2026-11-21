import assert from "node:assert/strict";
import {test} from "node:test";
import {generateBlocks} from "../docs/steiner-six-spectrum/widgets/blocks.mjs";

// This code runs in the reader's browser, independently of the Lean formalization.
// Index the unordered pair x < y by the number of pairs preceding (0, y), plus x.
function checkPairs(n) {
  const blocks = generateBlocks(n);
  const pairs = n * (n - 1) / 2;
  assert.equal(blocks.length, 6 * pairs / 15);
  const seen = new Uint8Array(Math.ceil(pairs / 8));
  for (let off = 0; off < blocks.length; off += 6) {
    for (let j = 1; j < 6; j++) {
      const y = blocks[off + j];
      assert(blocks[off + j - 1] < y && y < n);
      for (let i = 0; i < j; i++) {
        const index = y * (y - 1) / 2 + blocks[off + i];
        const mask = 1 << (index % 8);
        if (seen[index >> 3] & mask) assert.fail(`Duplicate pair in order ${n} at block ${off / 6 + 1}`);
        seen[index >> 3] |= mask;
      }
    }
  }
  // The block count gives exactly 'pairs' occurrences. Distinctness implies coverage.
}

test("finite recipes and recursive constructions cover each pair exactly once", () => {
  for (const n of [6, 31, 66, 76]) checkPairs(n);
  for (let n = 82; n <= 1641; n++) if (n % 15 === 1 || n % 15 === 6) checkPairs(n);
  for (const n of [1651, 1656, 8721, 8731, 9996]) checkPairs(n);
});

test("the generator rejects unsupported orders", () => {
  for (const n of [1, 16, 21, 32, 36, 46, 51, 61, 81, 10006, 31.5, NaN]) {
    assert.throws(() => generateBlocks(n), RangeError);
  }
});
