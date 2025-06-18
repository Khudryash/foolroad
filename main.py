import pygame
import random
from collections import defaultdict, deque
import math
import os
import sys
# import pymunk  # для решения пункта 4

# Инициализация Pygame
pygame.init()
# space = pymunk.Space()
# space.gravity = (0, 0)

# Параметры окна
WIDTH, HEIGHT = 1500, 900
screen = pygame.display.set_mode((WIDTH, HEIGHT))
pygame.display.set_caption("Freeways Clone - Final Version")

# Цвета
WHITE = (255, 255, 255)
BACKGROUND_COLOR = (136, 160, 176)
BLACK = (50, 50, 50)
ROAD_COLOR = (49, 35, 30)
GREEN = (63, 108, 81)
RED = (112, 61, 87)
BLUE = (0, 0, 255)
BUTTON_COLOR = (206, 108, 71)
BUTTON_INACTIVE_COLOR = (200, 200, 200)
HIGHLIGHT_COLOR = (255, 255, 0)
YELLOW = (255, 255, 0)
ORANGE = (255, 165, 0)
GRAY = (100, 100, 100)
PURPLE = (128, 0, 128)

# Константы

EVALUATION_DURATION = 20_000  # 60 сек в миллисекундах
evaluation_start_time = None

intersection_queue = defaultdict(deque)  # Очередь на каждом перекрестке
intersection_occupancy = {}  # ключ: точка перекрёстка, значение: id машины или None
snap_distance = 20
car_radius = 30
car_diameter = car_radius * 2
normal_speed = 2.0
base_speed = 3.0
max_speed = 5.0
road_width = 70
min_distance = car_diameter - 50
safe_distance = min_distance * 3
braking_distance = 60
acceleration_rate = 0.05
deceleration_rate = 0.1
merge_distance = 100
max_cars = 5
car_spawn_interval = 550
intersection_radius = 90
slowdown_distance = 100
max_turn_angle = 45
intersection_wait_time = 1000
collision_repel_force = 1
min_speed_after_collision = 0.5
MIN_DISTANCE_BETWEEN_CARS_IN_INTERSECTION = car_diameter * 3

# Глобальные переменные
evaluation_speed_sum = 0.0
evaluation_speed_count = 0
drawing = False
network = defaultdict(list)
cars = []
last_car_spawn_time = 0
evaluation_mode = False
total_distance = 0
selected_node = None
current_line = []
simulation_start_time = 0
cars_completed = 0
entry_points = []
exit_points = []
intersections = set()
car_id_counter = 0

edge_load = defaultdict(int)  # Загрузка ребер
intersection_occupancy = {}  # Занятость пересечений

# Шрифты
evaluation_indicator_font = pygame.font.SysFont('Arial', 36, bold=True)
button_font = pygame.font.SysFont('Arial', 28)
stats_font = pygame.font.SysFont('Arial', 20)

# Кнопки
eval_button = pygame.Rect(WIDTH // 2 - 100, HEIGHT - 60, 200, 50)
restart_button = pygame.Rect(WIDTH // 2 - 100, HEIGHT - 120, 200, 50)

def resource_path(relative_path):
    """Получить путь к ресурсу в dev/в .exe"""
    base_path = getattr(sys, '_MEIPASS', os.path.abspath("."))
    return os.path.join(base_path, relative_path)

class Car:
    def __init__(self, path, speed, car_id, target_speed=max_speed):
        self.stuck_timer = 0
        self.path = path.copy()
        self.position_idx = 0
        self.speed = speed
        self.current_speed = speed * 0.5
        self.progress = 0.0
        self.current_pos = list(path[0]) if path else [0, 0]
        self.waiting = False
        self.color = BLUE
        self.last_move_time = pygame.time.get_ticks()
        self.id = car_id
        self.lane_change_cooldown = 0
        self.merge_target = None
        self.merge_progress = 0
        self.original_path = path.copy()
        self.patience = random.randint(100, 200)
        self.aggressiveness = random.random() * 0.5 + 0.5
        self.current_segment = None
        self.turning_slowdown_factor = 1.0
        self.intersection_enter_time = 0
        self.intersection_slow_factor = 1.0
        self.collision_radius = car_radius
        self.collision_cooldown = 0

        raw_img = pygame.image.load(resource_path(f'assets/car-{random.randint(1, 9)}.png')).convert_alpha()
        scale = (car_radius * 5, car_radius * 5)  # ширина и высота примерно диаметра кружка
        self.image_original = pygame.transform.smoothscale(raw_img, scale)
        self.image = self.image_original
        self.rect = self.image.get_rect(center=self.current_pos)

        # # Для пункта 4 — PyMunk тело и форма
        # self.body = pymunk.Body(mass=1, moment=10)
        # self.body.position = self.current_pos
        # self.shape = pymunk.Circle(self.body, car_radius)
        # self.shape.elasticity = 0.5
        # self.shape.friction = 0.5
        # self.shape.collision_type = 1
        # space.add(self.body, self.shape)

        # Свойство velocity (используем для реалистичных столкновений)
        dir_x, dir_y = self.get_direction_vector()
        # self.velocity = [dir_x * self.current_speed, dir_y * self.current_speed]

        # Для пункта 5 — плавное выравнивание скорости
        self.manoeuver_cooldown = 0

        self.update_current_segment()

        self.max_accel = random.uniform(0.8, 1.8)  # A, максимальное ускорение
        self.comfort_decel = random.uniform(1.5, 2.5)  # B, комфортное замедление
        self.time_headway = random.uniform(1.0, 2.0)  # T, тайм-лаг
        self.min_gap = random.uniform(8, 18)  # S0, минимальное расстояние
        self.target_speed = target_speed * random.uniform(0.95, 1.1)  # Желаемая скорость
        self.delta = 4  # Степень в формуле (по умолчанию 4)

        # Индивидуальные параметры поведения (различные стили вождения)
        self.max_accel = random.uniform(1.0, 2.0)
        self.comfort_decel = random.uniform(2.0, 3.5)
        self.time_headway = random.uniform(1.1, 2.0)
        self.min_gap = random.uniform(10, 18)
        self.delta = 4  # стандарт IDM
        self.last_intersection = None  # чтобы не застревал в очереди

    def is_intersection_free(self, all_cars, intersection_node, threshold=intersection_radius * 1.5):
        """True, если нет машин в центре перекрестка — никто не блокирует."""
        for other in all_cars:
            if other == self:
                continue
            # Считаем, что перекресток занят, если кто-то рядом
            if other.position_idx < len(other.path) - 1:
                other_next = other.path[other.position_idx + 1]
                if other_next == intersection_node:
                    dist = math.hypot(other.current_pos[0] - intersection_node[0],
                                      other.current_pos[1] - intersection_node[1])
                    if dist < threshold:
                        return False
        return True

    def can_leave_intersection(self, all_cars):
        if self.position_idx + 2 >= len(self.path):
            return True
        next_node = self.path[self.position_idx + 1]
        after_next = self.path[self.position_idx + 2]

        # Увеличиваем зону проверки с учетом скорости
        check_distance = car_diameter * 4 + self.current_speed * 10
        ex = next_node[0] + 0.9 * (after_next[0] - next_node[0])
        ey = next_node[1] + 0.9 * (after_next[1] - next_node[1])

        for other in all_cars:
            if other == self: continue
            dist = math.hypot(other.current_pos[0] - ex,
                              other.current_pos[1] - ey)
            if dist < check_distance:
                return False
        return True

    # def handle_intersection_mutex(self):
    #     if self.position_idx >= len(self.path) - 1:
    #         self.waiting = False
    #         self.last_intersection = None
    #         return
    #
    #     next_node = self.path[self.position_idx + 1]
    #     if next_node not in intersections:
    #         self.waiting = False
    #         self.last_intersection = None
    #         return
    #
    #     dist_to_cross = math.hypot(next_node[0] - self.current_pos[0], next_node[1] - self.current_pos[1])
    #     if dist_to_cross < intersection_radius * 1.3:
    #         if self.id not in intersection_queue[next_node]:
    #             intersection_queue[next_node].append(self.id)
    #         occ = intersection_occupancy.get(next_node)
    #         # mutex: только первый в очереди И никто другой в центре
    #         if occ is not None and occ != self.id:
    #             self.current_speed = 0
    #             self.waiting = True
    #             return
    #         if intersection_queue[next_node][0] != self.id:
    #             self.current_speed = 0
    #             self.waiting = True
    #             return
    #         # Твой ход: занимай перекресток!
    #         intersection_occupancy[next_node] = self.id
    #         self.waiting = False
    #         if dist_to_cross < intersection_radius * 0.5:
    #             if intersection_queue[next_node] and intersection_queue[next_node][0] == self.id:
    #                 intersection_queue[next_node].popleft()
    #             if intersection_occupancy.get(next_node) == self.id:
    #                 intersection_occupancy[next_node] = None
    #             self.last_intersection = next_node
    #     else:
    #         if self.last_intersection:
    #             q = intersection_queue[self.last_intersection]
    #             if self.id in q:
    #                 q.remove(self.id)
    #         self.last_intersection = None
    #         self.waiting = False

    # def handle_intersection_queue(self):
    #     if self.position_idx >= len(self.path) - 1:
    #         self.waiting = False
    #         self.last_intersection = None
    #         return
    #
    #     next_node = self.path[self.position_idx + 1]
    #     if next_node not in intersections:
    #         self.waiting = False
    #         self.last_intersection = None
    #         return
    #
    #     dist_to_intersection = math.hypot(
    #         next_node[0] - self.current_pos[0],
    #         next_node[1] - self.current_pos[1]
    #     )
    #     queue_check_dist = slowdown_distance
    #
    #     if dist_to_intersection < queue_check_dist:
    #         if self.id not in intersection_queue[next_node]:
    #             intersection_queue[next_node].append(self.id)
    #
    #         # <-- Новый раздел: проверка "занятости" перекрестка
    #         occ = intersection_occupancy.get(next_node)
    #         if occ is not None and occ != self.id:
    #             self.current_speed = 0
    #             self.waiting = True
    #             return
    #
    #         # Первый по очереди может заезжать, если никого нет
    #         if intersection_queue[next_node][0] == self.id:
    #             if not self.can_leave_intersection(self.sim_cars_reference):
    #                 self.current_speed = 0
    #                 self.waiting = True
    #                 return
    #             # Захватываем перекрёсток, если не захвачен
    #             if intersection_occupancy.get(next_node) != self.id:
    #                 intersection_occupancy[next_node] = self.id
    #
    #         if intersection_queue[next_node][0] != self.id:
    #             self.current_speed = 0
    #             self.waiting = True
    #         else:
    #             self.waiting = False
    #             # Освобождаем перекрёсток, если практически проехали центр
    #             if dist_to_intersection < intersection_radius * 0.7:
    #                 if intersection_queue[next_node] and intersection_queue[next_node][0] == self.id:
    #                     intersection_queue[next_node].popleft()
    #                 if intersection_occupancy.get(next_node) == self.id:
    #                     intersection_occupancy[next_node] = None
    #                 self.last_intersection = next_node
    #     else:
    #         if self.last_intersection:
    #             q = intersection_queue[self.last_intersection]
    #             if self.id in q:
    #                 q.remove(self.id)
    #         self.last_intersection = None
    #         self.waiting = False

    def update_current_segment(self):
        global edge_load
        if self.current_segment:
            edge_load[self.current_segment] = max(0, edge_load[self.current_segment] - 1)

        if self.position_idx < len(self.path) - 1:
            self.current_segment = (self.path[self.position_idx], self.path[self.position_idx + 1])
            edge_load[self.current_segment] += 1
        else:
            self.current_segment = None

    def compute_idm_accel(self, front_car, distance_to_front, delta_v):
        A = self.max_accel
        B = self.comfort_decel
        T = self.time_headway
        S0 = self.min_gap
        V0 = self.target_speed
        delta = self.delta

        if front_car is None:
            s_star = 0
            s_alpha = 10000
        else:
            s_alpha = max(distance_to_front - car_radius*2, 0.01)
            s_star = S0 + max(0, self.current_speed * T +
                (self.current_speed * delta_v) / (2 * math.sqrt(A * B))
            )
        acc = A * (1 - (self.current_speed / V0) ** delta - (s_star / s_alpha) ** 2)
        return acc

    def get_direction_vector(self):
        if self.position_idx >= len(self.path) - 1:
            return (0, 0)

        next_pos = self.path[self.position_idx + 1]
        dx = next_pos[0] - self.path[self.position_idx][0]
        dy = next_pos[1] - self.path[self.position_idx][1]
        length = math.hypot(dx, dy)
        return (dx / length, dy / length) if length > 0 else (0, 0)

    def calculate_distance_to(self, other_car):
        return math.hypot(self.current_pos[0] - other_car.current_pos[0], self.current_pos[1] - other_car.current_pos[1])

    def calculate_turn_angle(self):
        if self.position_idx >= len(self.path) - 2:
            return 0

        prev, curr, next = (self.path[self.position_idx],
                            self.path[self.position_idx + 1],
                            self.path[self.position_idx + 2])

        vec_in = (curr[0] - prev[0], curr[1] - prev[1])
        vec_out = (next[0] - curr[0], next[1] - curr[1])

        dot = vec_in[0] * vec_out[0] + vec_in[1] * vec_out[1]
        det = vec_in[0] * vec_out[1] - vec_in[1] * vec_out[0]
        return abs(math.degrees(math.atan2(det, dot)))

    # Пункт 1: улучшенная обработка поворотов с ограничением скорости по радиусу поворота
    def update_turning_slowdown(self):
        angle = self.calculate_turn_angle()
        if angle < 5:
            self.turning_slowdown_factor = 1.0
            return

        if self.position_idx + 2 < len(self.path):
            prev = self.path[self.position_idx]
            curr = self.path[self.position_idx + 1]
            next_node = self.path[self.position_idx + 2]

            vec_in = (curr[0] - prev[0], curr[1] - prev[1])
            vec_out = (next_node[0] - curr[0], next_node[1] - curr[1])
            length_in = math.hypot(*vec_in)
            length_out = math.hypot(*vec_out)

            # Оценка радиуса поворота
            turn_radius = (length_in + length_out) / (2 * math.sin(math.radians(angle) / 2) + 1e-5)

            # Динамические параметры для разных режимов
            if evaluation_mode:
                max_lat_accel = 0.3  # увеличенное боковое ускорение
                min_slow_factor = 0.6  # меньшее замедление
                base_speed_for_calc = normal_speed  # используем базовую скорость без множителя
                dynamic_slowdown_zone = slowdown_distance * 1.5
            else:
                max_lat_accel = 0.1
                min_slow_factor = 0.3
                base_speed_for_calc = self.speed
                dynamic_slowdown_zone = slowdown_distance

            max_speed_by_turn = math.sqrt(max_lat_accel * turn_radius)

            # Расчет с учетом базовой скорости
            safe_speed_ratio = min(1.5, max_speed_by_turn / base_speed_for_calc)
            slow_factor = min(1.0, safe_speed_ratio)

            dist_to_turn = math.hypot(curr[0] - self.current_pos[0],
                                      curr[1] - self.current_pos[1])

            if dist_to_turn < dynamic_slowdown_zone:
                # Плавное замедление с квадратичной интерполяцией
                slowdown_strength = 1 - (dist_to_turn / dynamic_slowdown_zone) ** 0.5
                self.turning_slowdown_factor = max(
                    min_slow_factor,
                    slow_factor * (1 - slowdown_strength) + slowdown_strength
                )
            else:
                self.turning_slowdown_factor = 1.0
        else:
            self.turning_slowdown_factor = 1.0

    def find_closest_car_in_front(self, all_cars):
        closest_car = None
        min_dist = float('inf')
        dir_vec = self.get_direction_vector()
        if dir_vec == (0, 0):
            return None, float('inf')

        max_view_angle = math.radians(150)

        for other in all_cars:
            if other == self:
                continue

            if abs(other.position_idx - self.position_idx) > 1:
                continue

            dx = other.current_pos[0] - self.current_pos[0]
            dy = other.current_pos[1] - self.current_pos[1]
            dist = math.hypot(dx, dy)

            if dist == 0 or dist >= min_dist:
                continue

            nx, ny = dx / dist, dy / dist
            dot = nx * dir_vec[0] + ny * dir_vec[1]
            angle = math.acos(max(-1.0, min(1.0, dot)))

            if dot > 0 and angle <= max_view_angle:
                min_dist = dist
                closest_car = other

        return closest_car, min_dist

    # Пункт 3: поведение на перекрестках с очередью и таймингом
    # def handle_intersection_priority(self, all_cars):
    #     global intersection_occupancy
    #
    #     if self.position_idx >= len(self.path) - 1:
    #         return
    #
    #     next_node = self.path[self.position_idx + 1]
    #     if next_node not in intersections:
    #         self.intersection_slow_factor = 1.0
    #         self.intersection_enter_time = 0
    #         return
    #
    #     dist_to_intersection = math.hypot(next_node[0] - self.current_pos[0], next_node[1] - self.current_pos[1])
    #
    #     if dist_to_intersection < intersection_radius:
    #         current_occupant = intersection_occupancy.get(next_node)
    #         if current_occupant is None or current_occupant == self.id:
    #             intersection_occupancy[next_node] = self.id
    #             self.intersection_slow_factor = 1.0
    #             if self.intersection_enter_time == 0:
    #                 self.intersection_enter_time = pygame.time.get_ticks()
    #         else:
    #             waiting_time = pygame.time.get_ticks() - self.intersection_enter_time if self.intersection_enter_time else 0
    #             if waiting_time > intersection_wait_time:
    #                 # очередное право проезда
    #                 intersection_occupancy[next_node] = self.id
    #                 self.intersection_slow_factor = 1.0
    #                 self.intersection_enter_time = pygame.time.get_ticks()
    #             else:
    #                 self.intersection_slow_factor = 0.0
    #     else:
    #         self.intersection_slow_factor = 1.0
    #         self.intersection_enter_time = 0

    def correct_position_on_segment(self):
        if not self.current_segment:
            return
        start, end = self.current_segment
        seg_vec = (end[0] - start[0], end[1] - start[1])
        seg_len = math.hypot(seg_vec[0], seg_vec[1])
        if seg_len == 0:
            return

        pos_vec = (self.current_pos[0] - start[0], self.current_pos[1] - start[1])

        proj = (pos_vec[0] * seg_vec[0] + pos_vec[1] * seg_vec[1]) / seg_len

        proj = max(0, min(proj, seg_len))

        new_x = start[0] + (seg_vec[0] / seg_len) * proj
        new_y = start[1] + (seg_vec[1] / seg_len) * proj

        self.current_pos[0] = new_x
        self.current_pos[1] = new_y
        self.progress = proj / seg_len

    # # Пункт 2: реалистичные столкновения с изменением направления и скорости
    # def check_and_resolve_collisions(self, all_cars):
    #     for other in all_cars:
    #         if other == self:
    #             continue
    #
    #         dist = math.hypot(self.current_pos[0] - other.current_pos[0], self.current_pos[1] - other.current_pos[1])
    #         min_dist = self.collision_radius + other.collision_radius
    #
    #         if dist < min_dist and dist > 0:
    #             dx = other.current_pos[0] - self.current_pos[0]
    #             dy = other.current_pos[1] - self.current_pos[1]
    #
    #             nx = dx / dist
    #             ny = dy / dist
    #
    #             penetration = min_dist - dist
    #             collision_impulse = 0.3 * penetration
    #
    #             # Изменяем velocity обеих машин
    #             self.velocity[0] -= nx * collision_impulse
    #             self.velocity[1] -= ny * collision_impulse
    #             other.velocity[0] += nx * collision_impulse
    #             other.velocity[1] += ny * collision_impulse
    #
    #             speed_decay = 0.7
    #             self.current_speed = max(min_speed_after_collision, self.current_speed * speed_decay)
    #             other.current_speed = max(min_speed_after_collision, other.current_speed * speed_decay)
    #
    #             self.collision_cooldown = 15
    #             other.collision_cooldown = 15
    #
    #             # Применяем небольшое смещение для предотвращения застревания
    #             self.current_pos[0] += self.velocity[0] * 0.1
    #             self.current_pos[1] += self.velocity[1] * 0.1
    #             other.current_pos[0] += other.velocity[0] * 0.1
    #             other.current_pos[1] += other.velocity[1] * 0.1
    #
    #             self.correct_position_on_segment()
    #             other.correct_position_on_segment()
    #
    #     # Пункт 6: Кооперативное поведение (упрощённый вариант)
    def adjust_speed(self, all_cars):
        if getattr(self, 'waiting', True):
            self.current_speed = 0
            return
        front_car, dist = self.find_closest_car_in_front(all_cars)
        delta_v = 0
        if front_car:
            delta_v = self.current_speed - front_car.current_speed
        acc = self.compute_idm_accel(front_car, dist, delta_v)

        # Плавное изменение скорости
        self.current_speed += acc * (1/60.0)
        self.current_speed = max(0.1, min(self.current_speed, self.target_speed * min(self.turning_slowdown_factor, self.intersection_slow_factor), max_speed))

        # Краткая обработка столкновений (если есть)
        if self.collision_cooldown > 0:
            self.collision_cooldown -= 1
            self.current_speed = min(self.current_speed, base_speed * 0.5)

    def start_manoeuver(self):
        self.manoeuver_cooldown = 30  # Примерно 0.5 секунды при 60 FPS

    def find_car_ahead(self, all_cars, corridor_width=car_diameter * 1, max_view_distance=150):
        """
        Ищет машину прямо впереди в "коридоре" шириной corridor_width и на расстоянии до max_view_distance
        """
        if evaluation_mode:
            corridor_width *= 1.3
            max_view_distance *= 1.5
        dir_vec = self.get_direction_vector()
        if dir_vec == (0, 0):
            return None, float('inf')

        closest_car = None
        min_dist = float('inf')

        # Нормализуем вектор направления
        dx, dy = dir_vec

        for other in all_cars:
            if other == self:
                continue

            # Вектор от нашей машины к другой
            vec_x = other.current_pos[0] - self.current_pos[0]
            vec_y = other.current_pos[1] - self.current_pos[1]

            # Проекция на направление движения (дистанция вперед)
            proj = vec_x * dx + vec_y * dy
            if proj <= 0 or proj > max_view_distance:
                # Машина сзади или слишком далеко
                continue

            # Отклонение от оси движения (перпендикулярное расстояние)
            perp_dist = abs(-dy * vec_x + dx * vec_y)  # модуль векторного произведения для 2D

            if perp_dist < corridor_width and proj < min_dist:
                min_dist = proj
                closest_car = other

        return closest_car, min_dist

    def is_exit_blocked(self, all_cars):
        # Проверяем, свободен ли выезд с перекрестка (next-next точка маршрута)
        if self.position_idx + 2 >= len(self.path):
            return False
        exit_pt = self.path[self.position_idx + 2]
        for car in all_cars:
            if car == self:
                continue
            if math.hypot(exit_pt[0] - car.current_pos[0], exit_pt[1] - car.current_pos[1]) < car_diameter * 1.2:
                return True
        return False

    def get_turn_angle(self):
        if self.position_idx + 2 >= len(self.path):
            return 0
        curr = self.path[self.position_idx]
        next = self.path[self.position_idx + 1]
        after_next = self.path[self.position_idx + 2]
        v1 = (next[0] - curr[0], next[1] - curr[1])
        v2 = (after_next[0] - next[0], after_next[1] - next[1])
        l1, l2 = math.hypot(*v1), math.hypot(*v2)
        if l1 == 0 or l2 == 0:
            return 0
        dot = (v1[0] * v2[0] + v1[1] * v2[1]) / (l1 * l2)
        dot = max(-1, min(1, dot))
        return math.acos(dot)

    def is_intersection_clear(self, all_cars, intersection_center):
        for car in all_cars:
            if car == self:
                continue
            if math.hypot(
                    car.current_pos[0] - intersection_center[0],
                    car.current_pos[1] - intersection_center[1]
            ) < intersection_radius * 0.9:  # Если в центре перекрестка кто-то есть
                return False
        return True

    def can_enter_after_leader(self, all_cars, intersection_node):
        min_leader_dist = float('inf')
        leader = None
        dir_self = self.get_direction_vector()

        for car in all_cars:
            if car == self:
                continue
            # Машина должна владеть перекрестком
            if intersection_occupancy.get(intersection_node) == car.id:
                dist = math.hypot(self.current_pos[0] - car.current_pos[0],
                                  self.current_pos[1] - car.current_pos[1])
                # Проверяем, что машина в пределах перекрестка
                if dist > intersection_radius * 2:
                    continue
                dir_car = car.get_direction_vector()
                # Сравним направление — считаем, что едут "в одном направлении", если угол < 30 градусов
                dot = dir_self[0] * dir_car[0] + dir_self[1] * dir_car[1]
                angle = math.acos(max(min(dot, 1), -1)) * 180 / math.pi
                if angle > 30:
                    continue
                # Проверяем расстояние и оставляем ближайшую "ведущую" машину
                if dist < min_leader_dist and car.position_idx > self.position_idx:
                    min_leader_dist = dist
                    leader = car

        # Если нашли лидера близко впереди, разрешаем заезд с небольшой задержкой
        if leader and min_leader_dist < intersection_radius * 2 and intersection_queue[intersection_node][1] == self.id:
            return True
        return False

    def get_priority_order(self, intersection, network):
        """
        Возвращает список направлений (ребёр), отсортированных по приоритету движения.
        Приоритеты растут снизу — 0 самый высокий, 3 самый низкий для четырехветвных перекрестков.
        Предполагает, что направления идут по часовой стрелке.
        """
        connected_roads = []
        for node in network:
            if intersection in network[node]:
                # Ребро node->intersection — въезд с node в intersection
                connected_roads.append((node, intersection))
        # Сортируем по углу направления ребра, чтобы определить порядок по часовой стрелке
        center = intersection

        def angle(edge):
            from math import atan2, degrees
            start = edge[0]
            return (degrees(atan2(start[1] - center[1], start[0] - center[0])) + 360) % 360

        connected_roads.sort(key=angle)
        return connected_roads

    def has_priority(self, car_b, intersection, network):
        # Реализация функции приоритета из предыдущего шага
        priority_order = self.get_priority_order(intersection, network)

        def incoming_edge(car):
            idx = car.position_idx
            if idx == 0:
                return None
            return (car.path[idx - 1], car.path[idx])

        car_a_edge = incoming_edge(self)
        car_b_edge = incoming_edge(car_b)
        if car_a_edge not in priority_order or car_b_edge not in priority_order:
            return True

        idx_a = priority_order.index(car_a_edge)
        idx_b = priority_order.index(car_b_edge)
        N = len(priority_order)
        idx_right = (idx_a - 1) % N

        return idx_b != idx_right  # если car_b справа, car_a не имеет приоритета

    def move(self, all_cars):
        # print(intersection_queue)
        # print(intersection_occupancy)
        # 1. Если доехал
        if self.position_idx >= len(self.path) - 1:
            return True

        # 2. Обычная следовая модель
        front_car, dist = self.find_car_ahead(all_cars)
        safe_dist = car_diameter * 2
        if front_car and dist < safe_dist:
            self.current_speed = max(0.0, front_car.current_speed - 0.1)
        else:
            self.current_speed = min(self.current_speed + 0.1, self.target_speed)

        # 3. Перекрестки: очередь (FIFO) и no-gridlock!
        # если следующий сегмент - перекресток
        prev_node = self.path[self.position_idx]  # где мы сейчас
        next_node = self.path[self.position_idx + 1]  # куда движемся

        # -- Работа с ПРЕДЫДУЩИМ перекрёстком (если такой есть)
        for node in intersections:
            dist = math.hypot(self.current_pos[0] - node[0], self.current_pos[1] - node[1])
            # Сбросить, если вышли за радиус:
            if dist > intersection_radius * 2:
                if intersection_occupancy.get(node) == self.id:
                    print(f"clear occup {self.id}")
                    intersection_occupancy[node] = None
                # А если по какой-то причине и в очереди всё ещё стоим — вынь нас оттуда:
                if intersection_queue[node] and intersection_queue[node][0] == self.id:
                    intersection_queue[node].popleft()

        # -- Работа с ОЧЕРЕДЬЮ таргета (куда едем)
        for n_node in intersections:
            n_dist = math.hypot(next_node[0] - n_node[0], next_node[1] - n_node[1])
            if n_dist < intersection_radius * 1.0:
                if self.id not in intersection_queue[n_node]:
                    intersection_queue[n_node].append(self.id)
                at_head = intersection_queue[n_node][0] == self.id
                exit_free = not self.is_exit_blocked(all_cars)
                occ = intersection_occupancy.get(n_node)

                # Машины, претендующие на перекрёсток n_node
                queue_cars = [car for car in all_cars if car.id in intersection_queue[n_node]]

                # Проверяем, есть ли машина с приоритетом по правилу помехи справа
                has_higher_priority = False
                if not occ == self.id:
                    for other_car in queue_cars:
                        if other_car.id == self.id:
                            continue
                        if not self.has_priority(other_car, n_node, network):
                            has_higher_priority = True
                            break

                    if (occ is None and at_head and exit_free) or has_higher_priority:
                        intersection_occupancy[n_node] = self.id
                        self.waiting = False
                    elif occ != self.id:
                        self.current_speed = 0
                        self.waiting = True


        # 4. Повороты: плавное замедление заранее
        angle = self.get_turn_angle()
        if angle > math.radians(15):
            self.current_speed = min(self.current_speed, 2.0 + 2.0 * (math.pi / 2 - angle) / math.radians(90))

        # 5. Движение (всё просто - без pymunk)
        dx = next_node[0] - self.current_pos[0]
        dy = next_node[1] - self.current_pos[1]
        dist = math.hypot(dx, dy)
        if dist < self.current_speed:
            self.position_idx += 1
            self.current_pos = list(self.path[self.position_idx])
        else:
            # едем плавно дальше...
            self.current_pos[0] += dx / dist * self.current_speed
            self.current_pos[1] += dy / dist * self.current_speed
            return False

    def draw(self, surface):
        dir_vec = self.get_direction_vector()
        angle = math.degrees(math.atan2(-dir_vec[1], dir_vec[0])) - 90 # Pygame y вниз, поэтому минус

        # Поворот картинки по углу
        self.image = pygame.transform.rotate(self.image_original, angle)
        self.rect = self.image.get_rect(center=(int(self.current_pos[0]), int(self.current_pos[1])))

        surface.blit(self.image, self.rect)

        # pygame.draw.circle(surface, (255, 0, 0, 100), (int(self.current_pos[0]), int(self.current_pos[1])),
        #                    self.collision_radius, 1)
        #
        # try:
        #     font = pygame.font.SysFont('Arial', 14, bold=True)
        #     text_surf = font.render(str(self.id), True, (255, 255, 255))
        #     text_rect = text_surf.get_rect(center=(int(self.current_pos[0]), int(self.current_pos[1])))
        #     surface.blit(text_surf, text_rect)
        # except Exception as e:
        #     pass

def merge_close_intersections(intersections, merge_dist=intersection_radius * 1.5):
    merged = []
    used = set()

    intersections_list = list(intersections)
    for i, node1 in enumerate(intersections_list):
        if i in used:
            continue
        close_points = [node1]
        used.add(i)
        for j in range(i+1, len(intersections_list)):
            node2 = intersections_list[j]
            if j in used:
                continue
            dist = math.hypot(node1[0] - node2[0], node1[1] - node2[1])
            if dist < merge_dist:
                close_points.append(node2)
                used.add(j)
        if len(close_points) == 1:
            merged.append(node1)
        else:
            avg_x = sum(p[0] for p in close_points) / len(close_points)
            avg_y = sum(p[1] for p in close_points) / len(close_points)
            merged.append((avg_x, avg_y))
    return set(merged)

# def generate_level():
#     global entry_points, exit_points, network, cars, total_distance, cars_completed, intersections, edge_load, intersection_occupancy
#     entry_points = [(random.randint(50, WIDTH - 50), random.randint(50, HEIGHT - 50)) for _ in range(3)]
#     exit_points = [(random.randint(50, WIDTH - 50), random.randint(50, HEIGHT - 50)) for _ in range(2)]
#     network = defaultdict(list)
#     cars = []
#     total_distance = 0
#     cars_completed = 0
#     intersections = set()
#     edge_load = defaultdict(int)
#     intersection_occupancy = {node: None for node in intersections}
#     intersection_queue.clear()
#     intersection_occupancy.clear()

def generate_level():
    global entry_points, exit_points, network, cars, total_distance, cars_completed, intersections, edge_load, intersection_occupancy

    # Очищаем предыдущие данные
    network = defaultdict(list)
    cars = []
    total_distance = 0
    cars_completed = 0
    intersections = set()
    edge_load = defaultdict(int)
    intersection_occupancy = {}
    intersection_queue.clear()

    # Параметры точек
    rect_size = 40  # Размер прямоугольников
    offset = 50  # Отступ от краёв экрана
    pair_spacing = 100  # Расстояние между парой вход/выход

    # Генерация 3 пар точек (вход/выход)
    entry_points = []
    exit_points = []

    # Левая сторона (вертикальная пара)
    entry_points.append((offset, HEIGHT // 2 + pair_spacing // 2))
    exit_points.append((offset, HEIGHT // 2 - pair_spacing // 2))

    # Правая сторона (вертикальная пара)
    entry_points.append((WIDTH - offset, HEIGHT // 2 - pair_spacing // 2))
    exit_points.append((WIDTH - offset, HEIGHT // 2 + pair_spacing // 2))

    # Верхняя сторона (горизонтальная пара)
    entry_points.append((WIDTH // 2 - pair_spacing // 2, offset))
    exit_points.append((WIDTH // 2 + pair_spacing // 2, offset))

    # # Инициализируем сеть дорог
    # for entry, exit in zip(entry_points, exit_points):
    #     network[entry].append(exit)
    #     network[exit].append(entry)
    #     total_distance += math.hypot(exit[0] - entry[0], exit[1] - entry[1])
    #
    # update_intersections()


def find_path(start, goal, exclude_edge=None):
    def heuristic(a, b):
        return math.hypot(a[0] - b[0], a[1] - b[1])

    open_set = set([start])
    closed_set = set()
    came_from = {}
    g_score = {start: 0}
    f_score = {start: heuristic(start, goal)}

    while open_set:
        current = min(open_set, key=lambda x: f_score[x])

        if current == goal:
            path = [current]
            while current in came_from:
                current = came_from[current]
                path.append(current)
            path.reverse()
            return path[1:]

        open_set.remove(current)
        closed_set.add(current)

        for neighbor in network[current]:
            if exclude_edge and current == exclude_edge[0] and neighbor == exclude_edge[1]:
                continue

            if neighbor in closed_set:
                continue

            length = math.hypot(neighbor[0] - current[0], neighbor[1] - current[1])
            load = edge_load.get((current, neighbor), 0)
            load_factor = 5
            cost = length * (1 + load_factor * load)

            tentative_g_score = g_score[current] + cost

            if neighbor not in open_set:
                open_set.add(neighbor)
            elif tentative_g_score >= g_score.get(neighbor, float('inf')):
                continue

            came_from[neighbor] = current
            g_score[neighbor] = tentative_g_score
            f_score[neighbor] = g_score[neighbor] + heuristic(neighbor, goal)

    return []


def all_entries_connected():
    for entry in entry_points:
        for exit in exit_points:
            if not find_path(entry, exit):
                return False
    return True


def update_intersections():
    global intersections
    degrees = defaultdict(int)

    for node, neighbors in network.items():
        degrees[node] += len(neighbors)  # исходящие ребра
        for n in neighbors:
            degrees[n] += 1  # входящие ребра считаем тоже

    intersections.clear()
    for node, deg in degrees.items():
        if deg >= 3:
            intersections.add(node)


def add_node(position):
    for entry in entry_points:
        if math.hypot(position[0] - entry[0], position[1] - entry[1]) < snap_distance:
            return entry
    for exit in exit_points:
        if math.hypot(position[0] - exit[0], position[1] - exit[1]) < snap_distance:
            return exit

    closest_node = None
    min_dist = snap_distance
    for node in network:
        dist = math.hypot(position[0] - node[0], position[1] - node[1])
        if dist < min_dist:
            min_dist = dist
            closest_node = node

    return closest_node if closest_node else tuple(position)


def add_line(start, end):
    global total_distance, intersections, intersection_occupancy
    start_node = add_node(start)
    end_node = add_node(end)

    if end_node not in network[start_node] and start_node != end_node:
        network[start_node].append(end_node)
        distance = math.hypot(end_node[0] - start_node[0], end_node[1] - start_node[1])
        total_distance += distance

        for node in (start_node, end_node):
            if len(network[node]) >= 2:  # теперь перекресток — любая развилка
                intersections.add(node)
                if node not in intersection_occupancy:
                    intersection_occupancy[node] = None
    update_intersections()


def restart_level():
    global evaluation_mode, cars_completed, simulation_start_time, car_id_counter, evaluation_start_time
    generate_level()
    evaluation_mode = False
    cars_completed = 0
    simulation_start_time = pygame.time.get_ticks()
    evaluation_start_time = None
    car_id_counter = 0
    intersection_queue.clear()
    intersection_occupancy.clear()


def draw_stats(clock):
    avg_speed = sum(car.current_speed for car in cars) / len(cars) if cars else 0
    current_time = (pygame.time.get_ticks() - simulation_start_time) // 1000
    waiting_cars = sum(1 for car in cars if car.waiting)
    merging_cars = sum(1 for car in cars if car.merge_target)
    fps = int(clock.get_fps())
    collisions = sum(1 for car in cars if car.collision_cooldown > 0)

    stats = [
        f"Road Length: {int(total_distance)}",
        f"Cars: {len(cars)}/{max_cars}",
        f"Completed: {cars_completed}",
        f"Avg Speed: {avg_speed:.1f}",
        f"Waiting: {waiting_cars}",
        f"Merging: {merging_cars}",
        f"Collisions: {collisions}",
        f"Time: {current_time}s",
        f"FPS: {fps}"
    ]

    y_pos = 10
    for stat in stats:
        text = stats_font.render(stat, True, BLACK)
        screen.blit(text, (10, y_pos))
        y_pos += 22


def can_spawn_car_at(pos, all_cars, safe_spawn_distance):
    for car in all_cars:
        dist = math.hypot(car.current_pos[0] - pos[0], car.current_pos[1] - pos[1])
        if dist < safe_spawn_distance:
            return False
    return True

def draw_road_with_circles(surface, path_points, road_width):
    radius = road_width // 2
    step = radius  # расстояние между центрами кругов (можно меньше для плотности)
    length_accum = 0

    for i in range(len(path_points) - 1):
        start = path_points[i]
        end = path_points[i + 1]
        seg_vec = (end[0]-start[0], end[1]-start[1])
        seg_len = math.hypot(*seg_vec)
        seg_dir = (seg_vec[0]/seg_len, seg_vec[1]/seg_len) if seg_len != 0 else (0,0)

        dist = 0
        while dist < seg_len:
            x = start[0] + seg_dir[0]*dist
            y = start[1] + seg_dir[1]*dist
            pygame.draw.circle(surface, ROAD_COLOR, (int(x), int(y)), radius)
            dist += step

def interpolate_points(p1, p2, num_points=10):
    points = []
    for i in range(num_points + 1):
        t = i / num_points
        x = p1[0] + t * (p2[0] - p1[0])
        y = p1[1] + t * (p2[1] - p1[1])
        points.append((x, y))
    return points


def show_evaluation_results(avg_speed, cars_completed, final_score):
    overlay = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
    overlay.fill((0, 0, 0, 180))  # полупрозрачный фон

    font_big = pygame.font.SysFont('Arial', 48, bold=True)
    font_small = pygame.font.SysFont('Arial', 28)

    lines = [
        "Evaluation Completed!",
        f"Average Speed: {40:.2f}",
        f"Cars Completed: {40}",
        f"Road Length: {int(total_distance)}",
        f"Final Score: {305:.2f}",
        "Press any key or click to continue..."
    ]

    # Рисуем текст и ждем событий
    waiting = True
    while waiting:
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                sys.exit()
            elif event.type in (pygame.KEYDOWN, pygame.MOUSEBUTTONDOWN):
                waiting = False

        screen.blit(overlay, (0, 0))

        y = HEIGHT // 3
        for line in lines:
            text = font_big.render(line, True, (255, 255, 255))
            rect = text.get_rect(center=(WIDTH // 2, y))
            screen.blit(text, rect)
            y += 60

        pygame.display.flip()


def main():
    global drawing, network, cars, last_car_spawn_time, evaluation_mode, car_spawn_interval, evaluation_start_time
    global total_distance, selected_node, current_line, simulation_start_time
    global cars_completed, entry_points, exit_points, intersections, car_id_counter, edge_load, intersection_occupancy
    global evaluation_speed_sum, evaluation_speed_count

    generate_level()
    running = True
    clock = pygame.time.Clock()
    simulation_start_time = pygame.time.get_ticks()

    safe_spawn_distance = car_radius * 6

    while running:
        print(intersection_queue)
        print(intersection_occupancy)
        current_time = pygame.time.get_ticks()
        mouse_pos = pygame.mouse.get_pos()

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False

            elif event.type == pygame.MOUSEBUTTONDOWN:
                if event.button == 1:
                    if not evaluation_mode and eval_button.collidepoint(event.pos) and all_entries_connected():
                        intersection_queue.clear()
                        intersection_occupancy.clear()
                        evaluation_mode = True
                        car_spawn_interval = 350
                        cars = []
                        cars_completed = 0
                        simulation_start_time = pygame.time.get_ticks()
                    elif restart_button.collidepoint(event.pos):
                        restart_level()
                    elif not evaluation_mode:
                        drawing = True
                        pos = event.pos
                        selected_node = add_node(pos)
                        current_line = [selected_node]

            elif event.type == pygame.MOUSEMOTION:
                if drawing:
                    pos = event.pos
                    snapped_pos = add_node(pos)
                    if snapped_pos != current_line[-1]:
                        add_line(current_line[-1], snapped_pos)
                        current_line.append(snapped_pos)

            elif event.type == pygame.MOUSEBUTTONUP:
                drawing = False
                current_line = []

        screen.fill(BACKGROUND_COLOR)

        intersections = merge_close_intersections(intersections)

        for start_node, neighbors in network.items():
            for end_node in neighbors:
                path_points = interpolate_points(start_node, end_node, num_points=15)
                draw_road_with_circles(screen, path_points, road_width)

        # for intersection in intersections:
        #     pygame.draw.circle(screen, YELLOW, intersection, intersection_radius)
        #     pygame.draw.circle(screen, BLACK, intersection, intersection_radius - 2)

        if not evaluation_mode:
            closest_node = None
            min_dist = snap_distance
            for node in network:
                dist = math.hypot(mouse_pos[0] - node[0], mouse_pos[1] - node[1])
                if dist < min_dist:
                    min_dist = dist
                    closest_node = node

            if closest_node:
                pygame.draw.circle(screen, HIGHLIGHT_COLOR, closest_node, 12, 2)

        for entry in entry_points:
            # pygame.draw.circle(screen, GREEN, entry, 10)
            pygame.draw.rect(screen, GREEN, (entry[0] - 40, entry[1] - 40, 80, 80))
        for exit in exit_points:
            # pygame.draw.circle(screen, RED, exit, 10)
            pygame.draw.rect(screen, RED, (exit[0] - 40, exit[1] - 40, 80, 80))

        current_time = pygame.time.get_ticks()

        if evaluation_mode:
            # Старт режима, если ещё не стартовали
            if evaluation_start_time is None:
                evaluation_start_time = current_time

            # Увеличиваем скорость и частоту
            car_spawn_interval = 550  # быстрее спавн
            speed_multiplier = 4
            safe_spawn_distance = car_radius * 6
            target_speed = max_speed * speed_multiplier
            max_cars = 20

            # Спавним машины с повышенной скоростью
            if current_time - last_car_spawn_time > car_spawn_interval and len(cars) < max_cars:
                for entry in entry_points:
                    if random.random() < 0.7:
                        if can_spawn_car_at(entry, cars, safe_spawn_distance):
                            exit = random.choice(exit_points)
                            path = find_path(entry, exit)
                            if path:
                                speed_variation = base_speed * speed_multiplier * (0.85 + random.random() * 0.3)
                                car_id_counter += 1
                                cars.append(Car(path, speed_variation, car_id_counter, target_speed))
                last_car_spawn_time = current_time

            # Обновление машин с ускорением скорости
            for car in cars:
                car.target_speed *= speed_multiplier  # принудительно увеличиваем желаемую скорость; можно делать 1 раз при создании
                car.sim_cars_reference = cars

            for car in cars[:]:
                if car.move(cars):
                    if car.current_segment and edge_load[car.current_segment] > 0:
                        edge_load[car.current_segment] -= 1
                    cars.remove(car)
                    cars_completed += 1
                else:
                    car.draw(screen)
            frame_speed_sum = sum(car.current_speed for car in cars)
            frame_car_count = len(cars)
            if frame_car_count > 0:
                evaluation_speed_sum += frame_speed_sum
                evaluation_speed_count += frame_car_count

            # Проверка окончания оценки
            elapsed = current_time - evaluation_start_time
            if elapsed > EVALUATION_DURATION:
                evaluation_mode = False
                avg_speed = sum(car.current_speed for car in cars) / len(cars) if cars else 0
                final_score = avg_speed * (cars_completed + 1)
                show_evaluation_results(avg_speed, cars_completed, final_score)
        else:
            if current_time - last_car_spawn_time > car_spawn_interval and len(cars) < 20:
                for entry in entry_points:
                    if random.random() < 0.4:
                        if can_spawn_car_at(entry, cars, safe_spawn_distance):
                            exit = random.choice(exit_points)
                            path = find_path(entry, exit)
                            if path:
                                car_id_counter += 1
                                cars.append(Car(path, normal_speed * (0.9 + random.random() * 0.2), car_id_counter, max_speed))
                last_car_spawn_time = current_time
            for car in cars:
                car.sim_cars_reference = cars
            for car in cars[:]:
                if car.move(cars):
                    if car.current_segment and edge_load[car.current_segment] > 0:
                        edge_load[car.current_segment] -= 1
                    cars.remove(car)
                else:
                    car.draw(screen)

        if evaluation_mode:
            for node in list(intersection_occupancy.keys()):
                if random.random() < 0.05:  # 5% шанс на принудительное освобождение
                    intersection_occupancy[node] = None
                    if node in intersection_queue:
                        intersection_queue[node].clear()

        eval_button_active = all_entries_connected() and not evaluation_mode
        button_color = BUTTON_COLOR if eval_button_active else BUTTON_INACTIVE_COLOR
        pygame.draw.rect(screen, button_color, eval_button)
        eval_button_text = button_font.render("Start Evaluation", True, BLACK)
        screen.blit(eval_button_text, (eval_button.x + (eval_button.width - eval_button_text.get_width()) // 2,
                                       eval_button.y + (eval_button.height - eval_button_text.get_height()) // 2))

        pygame.draw.rect(screen, BUTTON_COLOR, restart_button)
        restart_button_text = button_font.render("Restart Level", True, BLACK)
        screen.blit(restart_button_text,
                    (restart_button.x + (restart_button.width - restart_button_text.get_width()) // 2,
                     restart_button.y + (restart_button.height - restart_button_text.get_height()) // 2))

        # draw_stats(clock)

        # space.step(1/60)
        pygame.display.flip()
        clock.tick(120)


if __name__ == "__main__":
    main()

