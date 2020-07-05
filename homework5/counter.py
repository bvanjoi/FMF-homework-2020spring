# counter.py

counter = 0


def fresh_var():
    global counter
    c = counter
    counter = counter + 1
    return 'x_'+(c.__str__())
