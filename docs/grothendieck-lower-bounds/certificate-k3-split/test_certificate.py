def put(path, rows):
    path.write_text("".join(" ".join(map(str, row)) + "\n" for row in rows))
