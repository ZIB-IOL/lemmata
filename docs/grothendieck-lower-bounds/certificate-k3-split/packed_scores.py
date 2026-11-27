"""Pack all signed column sums into disjoint 64-bit digits of one Python integer."""

import struct


class Scores:
    def __init__(self, matrix):
        n, m = len(matrix), len(matrix[0])
        self.width = 8 * m
        half = 1 << 63
        assert all(len(row) == m for row in matrix)
        assert all(sum(map(abs, col)) < half for col in zip(*matrix))

        def pack(row):
            value = 0
            for t in reversed(row):
                value = (value << 64) + t
            return value

        packed = [pack(row) for row in matrix]
        self.offset = pack([half] * m) + sum(packed)
        self.tables = []
        for i in range(0, n, 8):
            group = packed[i : i + 8]
            table = [0] * (1 << len(group))
            for j in range(1, len(table)):
                bit = j & -j
                table[j] = table[j - bit] + 2 * group[bit.bit_length() - 1]
            self.tables.append(table)
        self.unpack = struct.Struct("<" + "Q" * m).unpack

    def __call__(self, mask):
        value = self.offset - sum(
            t[b] for t, b in zip(self.tables, mask.to_bytes(20, "little"))
        )
        return sum(
            abs(v - (1 << 63)) for v in self.unpack(value.to_bytes(self.width, "little"))
        )
