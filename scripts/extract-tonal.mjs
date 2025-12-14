#!/usr/bin/env node
// Extract scales, chords, and intervals from tonal.js as pitch class sets
// Run with: npx tonal && node scripts/extract-tonal.mjs

import { ScaleType, ChordType, Interval } from "tonal";

// Convert interval name to semitones (pitch class)
function intervalToPC(ivl) {
  const semitones = Interval.semitones(ivl);
  return semitones !== undefined ? semitones % 12 : null;
}

// Convert interval string to pitch class set
function intervalsToPCS(intervals) {
  return intervals
    .split(" ")
    .map(intervalToPC)
    .filter(pc => pc !== null)
    .sort((a, b) => a - b);
}

// Rotate a PCS by k semitones (transpose down by k)
function rotatePCS(pcs, k) {
  return pcs.map(pc => (pc + 12 - k) % 12).sort((a, b) => a - b);
}

// Compute interval vector (gaps between adjacent notes, including wraparound)
function intervalVector(pcs) {
  if (pcs.length === 0) return [];
  if (pcs.length === 1) return [12];
  const iv = [];
  for (let i = 0; i < pcs.length; i++) {
    const next = (i + 1) % pcs.length;
    const gap = next === 0 ? (pcs[0] + 12 - pcs[i]) : (pcs[next] - pcs[i]);
    iv.push(gap);
  }
  return iv;
}

// Compare interval vectors lexicographically
function ivLt(iv1, iv2) {
  for (let i = 0; i < Math.min(iv1.length, iv2.length); i++) {
    if (iv1[i] < iv2[i]) return true;
    if (iv1[i] > iv2[i]) return false;
  }
  return iv1.length < iv2.length;
}

// Compute normal form (most compact rotation)
function normalForm(pcs) {
  if (pcs.length === 0) return [];
  let best = pcs;
  let bestIV = intervalVector(pcs);
  for (let k = 1; k < 12; k++) {
    const rotated = rotatePCS(pcs, k);
    const iv = intervalVector(rotated);
    if (ivLt(iv, bestIV)) {
      best = rotated;
      bestIV = iv;
    }
  }
  return best;
}

// Convert PCS to bitset
function pcsToBits(pcs) {
  let bits = 0;
  for (const pc of pcs) {
    bits |= (1 << pc);
  }
  return bits;
}

// Compute normal form bits
function normalFormBits(pcs) {
  return pcsToBits(normalForm(pcs));
}

// Extract all scales
const scales = {};
for (const scale of ScaleType.all()) {
  if (scale.intervals.length > 0) {
    const pcs = intervalsToPCS(scale.intervals.join(" "));
    scales[scale.name] = {
      bits: pcsToBits(pcs),
      normalFormBits: normalFormBits(pcs),
      aliases: scale.aliases,
    };
  }
}

// Extract all chords
const chords = {};
for (const chord of ChordType.all()) {
  if (chord.intervals.length > 0) {
    // Use name if available, otherwise first alias
    const name = chord.name || chord.aliases[0] || null;
    if (name) {
      const pcs = intervalsToPCS(chord.intervals.join(" "));
      chords[name] = {
        bits: pcsToBits(pcs),
        normalFormBits: normalFormBits(pcs),
        aliases: chord.name ? chord.aliases : chord.aliases.slice(1),
      };
    }
  }
}

// Standard intervals (within octave)
const intervals = {
  "perfect unison": 0,
  "minor second": 1,
  "major second": 2,
  "minor third": 3,
  "major third": 4,
  "perfect fourth": 5,
  "tritone": 6,
  "perfect fifth": 7,
  "minor sixth": 8,
  "major sixth": 9,
  "minor seventh": 10,
  "major seventh": 11,
};

const output = {
  meta: {
    source: "tonal.js",
    convention: "C = 0",
    generated: new Date().toISOString(),
  },
  intervals,
  scales,
  chords,
};

console.log(JSON.stringify(output, null, 2));
