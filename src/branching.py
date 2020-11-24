from random import choice

class ERMA:
    def __init__(self, xs, alpha=0.4, alpha_dec=10**(-6), alpha_lb=0.06):
        self.alpha = alpha
        self.alpha_dec = alpha_dec
        self.alpha_lb = alpha_lb
        self.q = {x: 0 for x in xs}
        self.learned_count = 0
        self.last_assigned = {x: 0 for x in xs}
        self.participated = {x: 0 for x in xs}

    
    def after_conflict(self, learned, conflict):
        self.learned_count += 1
        for v in set(learned.vars()) | set(conflict.vars()):
            self.participated[v] += 1
        if self.alpha > self.alpha_lb:
            self.alpha -= self.alpha_dec
    
    def on_assign(self, x):
        self.last_assigned[x] = self.learned_count
        self.participated[x] = 0
    
    def on_unassign(self, xs):
        for x in xs:
            interval = self.learned_count - self.last_assigned[x]
            if interval > 0:
                r = self.participated[x] / interval
                self.q[x] = (1 - self.alpha) * self.q[x] + self.alpha * r

    def pick(self, free):
        q, x = max([(self.q[x], x) for x in free], key=lambda p:p[0])
        return x