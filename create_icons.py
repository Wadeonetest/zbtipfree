import os
import struct

def create_png(width, height):
    signature = b'\x89PNG\r\n\x1a\n'
    
    def crc32(data):
        crc = 0xffffffff
        table = [0] * 256
        for i in range(256):
            c = i
            for _ in range(8):
                c = (c >> 1) ^ 0xedb88320 if c & 1 else c >> 1
            table[i] = c
        for byte in data:
            crc = table[(crc ^ byte) & 0xff] ^ (crc >> 8)
        return (crc ^ 0xffffffff) & 0xffffffff
    
    def chunk(type_bytes, data):
        length = struct.pack('>I', len(data))
        crc_data = type_bytes + data
        crc = struct.pack('>I', crc32(crc_data))
        return length + type_bytes + data + crc
    
    ihdr = struct.pack('>IIBBBBB', width, height, 8, 6, 0, 0, 0)
    ihdr_chunk = chunk(b'IHDR', ihdr)
    
    raw_data = []
    for y in range(height):
        raw_data.append(0)
        for x in range(width):
            r = (x * 255) // width
            g = (y * 255) // height
            b = 128
            a = 255
            raw_data.extend([r, g, b, a])
    
    import zlib
    compressed = zlib.compress(bytes(raw_data))
    idat_chunk = chunk(b'IDAT', compressed)
    
    iend_chunk = chunk(b'IEND', b'')
    
    return signature + ihdr_chunk + idat_chunk + iend_chunk

assets_dir = 'Assets'
if not os.path.exists(assets_dir):
    os.makedirs(assets_dir)

icons = [
    ('StoreLogo.png', 50, 50),
    ('Square150x150Logo.png', 150, 150),
    ('Square44x44Logo.png', 44, 44),
    ('Wide310x150Logo.png', 310, 150),
    ('Square310x310Logo.png', 310, 310),
    ('SmallTile.png', 71, 71),
    ('SplashScreen.png', 620, 300),
    ('Square71x71Logo.png', 71, 71),
]

for name, width, height in icons:
    png_data = create_png(width, height)
    with open(os.path.join(assets_dir, name), 'wb') as f:
        f.write(png_data)
    print(f'Created {name} ({width}x{height})')

print('All icons created successfully!')
