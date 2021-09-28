register _PC : bits(64)

enum read_kind = {
  Read_plain,
  Read_ifetch
}

// Work-around to prevent read_kind disappearing
register dummy: read_kind
