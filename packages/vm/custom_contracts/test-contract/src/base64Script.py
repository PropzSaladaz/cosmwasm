import base64

LIST = "L"
INT = "I"

data = input("input the data: ")
[command, data] = data.split(':')

if (command == LIST):
    data = bytes([int(x) for x in data.strip('[] ').split(',')])
elif (command == INT):
    data = int(data).to_bytes((int(data).bit_length()+7) // 8, 'big')
print("encoded: ", base64.b64encode(data)) 