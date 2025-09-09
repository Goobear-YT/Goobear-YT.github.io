from PIL import Image, ImageTk
import tkinter as tk
from tkinter import filedialog
import math

# --- Constants ---
FRAME_SIZE = 32
SCALE_FACTOR = 2
BODY_OFFSET_Y = 12
HAT_FRAME_SIZE = 48
HAT_OFFSET_Y = -18
ANIMATION_DELAY_MS = int(0.05 * 1000)  # use ms for after()
BG_SIZE = 500  # logical size (unscaled)
CANVAS_SIZE = BG_SIZE

# Keep the player ~32px (logical) away from background edges
BORDER_MARGIN_LOGICAL = 32
BORDER_MARGIN = BORDER_MARGIN_LOGICAL * SCALE_FACTOR

# Movement constants
MOVE_SPEED = 8                     # logical px per tick
TICK_MS = ANIMATION_DELAY_MS       # keep movement & animation in sync
MAX_KEYS_HELD = 5                  # cap queued keypresses (anti-lag)

# Locked coordinates (make sure list order matches VIEW_ORDER!)
VIEW_ORDER = ['back', 'left', 'front', 'right']

# --- Hat positions ---
HAT_FRAME_POSITIONS = {
    'idle': {
        'back':  (0, 0),
        'left':  (48, 0),
        'front': (96, 0),
        'right': (144, 0),
    },
    'grab': {
        'back':  (0, 0),   # special case → idle back
        'left':  (48, 48),
        'front': (96, 48),
        'right': (144, 48),
    },
    'action': {
        'back':  (0, 0),
        'left':  (48, 0),
        'front': (96, 0),
        'right': (144, 0),
    },
    'damage': {
        'back':  (0, 0),
        'left':  (48, 0),
        'front': (96, 0),
        'right': (144, 0),
    },
    'death': {
        'back': (0, 96),  # only one frame but we store it in dict format for consistency
        'left': (0, 96),
        'front': (0, 96),
        'right': (0, 96),
    }
}

# --- Head positions ---
HEAD_FRAME_POSITIONS = {
    'idle': {
        'back':  0,
        'left':  32,
        'front': 64,
        'right': 96,
    },
    'grab': {
        'back':  272,
        'left':  176,
        'front': 208,
        'right': 240,
    },
    'action': {
        'back':  272,
        'left':  304,
        'front': 336,
        'right': 368,
    },
    'damage': {
        'back':  400,
        'left':  432,
        'front': 464,
        'right': 496,
    },
    'death': {
        'back':  528,
        'left':  528,
        'front': 528,
        'right': 528,
    }
}

# --- Body positions ---
BODY_DAMAGE_COORDS = {
    'back':  (32, 608),
    'left':  (32, 640),
    'front': (96, 608),
    'right': (96, 640)
}
BODY_DEATH_COORDS = {
    'back':  (32, 672),
    'left':  (32, 672),
    'front': (32, 672),
    'right': (32, 672)
}

# Walking head bob offsets (index 0..4)
HEAD_BOB_OFFSETS = [1, 0, -1, 0, 1]
HAT_BOB_OFFSETS = [1, 0, -1, 0, 1]
# Helpers to map direction -> head rows
def head_action_y(direction):
    return {
        'back':  HEAD_FRAME_POSITIONS['action_back'],
        'left':  HEAD_FRAME_POSITIONS['action_left'],
        'front': HEAD_FRAME_POSITIONS['action_front'],
        'right': HEAD_FRAME_POSITIONS['action_right'],
    }[direction]

def head_damage_y(direction):
    return {
        'back':  HEAD_FRAME_POSITIONS['damage_back'],
        'left':  HEAD_FRAME_POSITIONS['damage_left'],
        'front': HEAD_FRAME_POSITIONS['damage_front'],
        'right': HEAD_FRAME_POSITIONS['damage_right'],
    }[direction]

def hat_action_y(direction):
    return {
        'back':  HAT_FRAME_POSITIONS['action_back'],
        'left':  HAT_FRAME_POSITIONS['action_left'],
        'front': HAT_FRAME_POSITIONS['action_front'],
        'right': HAT_FRAME_POSITIONS['action_right'],
    }[direction]

def hat_damage_y(direction):
    return {
        'back':  HAT_FRAME_POSITIONS['damage_back'],
        'left':  HAT_FRAME_POSITIONS['damage_left'],
        'front': HAT_FRAME_POSITIONS['damage_front'],
        'right': HAT_FRAME_POSITIONS['damage_right'],
    }[direction]

class SpriteViewerApp:
    def __init__(self, root):
        self.root = root
        self.root.title("GoobView")

        # Canvas
        self.canvas = tk.Canvas(root, width=CANVAS_SIZE, height=CANVAS_SIZE, bg="green")
        self.canvas.pack()

        # Buttons
        self.btn_frame = tk.Frame(root)
        self.btn_frame.pack(pady=4)
        tk.Button(self.btn_frame, text="Load Background", command=self.load_background).pack(side=tk.LEFT, padx=2)
        tk.Button(self.btn_frame, text="Load Hat", command=self.load_hat).pack(side=tk.LEFT, padx=2)
        tk.Button(self.btn_frame, text="Load Head", command=self.load_head).pack(side=tk.LEFT, padx=2)
        tk.Button(self.btn_frame, text="Load Body", command=self.load_body).pack(side=tk.LEFT, padx=2)

        # Defaults
        self.hat_img = self.safe_open_rgba("Noob_Hat.png")
        self.head_img = self.safe_open_rgba("Noob_Head.png")
        self.body_img = self.safe_open_rgba("Noob_Body.png")

        # Background
        from PIL import Image  # local import to avoid confusion
        self.background = Image.new("RGBA", (BG_SIZE, BG_SIZE), (0, 255, 0, 255))
        self.bg_scaled = self.background.resize((CANVAS_SIZE, CANVAS_SIZE), Image.NEAREST)

        # World position
        self.bg_offset_x = 0.0
        self.bg_offset_y = 0.0

        # State
        self.facing = 'front'
        self._anim_after_id = None
        self._move_after_id = None
        self.keys_down = set()
        self.key_queue = []
        self.walk_frame_idx = 0
        self.zoom = 1.0
        
        # Key bindings
        self.root.bind('<KeyPress-w>', self.on_key_press)
        self.root.bind('<KeyPress-a>', self.on_key_press)
        self.root.bind('<KeyPress-s>', self.on_key_press)
        self.root.bind('<KeyPress-d>', self.on_key_press)
        self.root.bind('<KeyRelease-w>', self.on_key_release)
        self.root.bind('<KeyRelease-a>', self.on_key_release)
        self.root.bind('<KeyRelease-s>', self.on_key_release)
        self.root.bind('<KeyRelease-d>', self.on_key_release)
        for key in ['i','j','k','l','f','g','h']:
            self.root.bind(key, lambda e, k=key: self.handle_action_key(k))

        # Mouse wheel zoom
        self.root.bind("<MouseWheel>", self.on_mousewheel)   # Windows
        self.root.bind("<Button-4>", self.on_mousewheel)     # Linux scroll up
        self.root.bind("<Button-5>", self.on_mousewheel)     # Linux scroll down

# Initial frame
        idle = self.get_combined_frame('idle', self.facing)

# Create initial PhotoImages
        self.bg_tk = ImageTk.PhotoImage(self.bg_scaled, master=self.canvas)
        self.player_tk = ImageTk.PhotoImage(idle, master=self.canvas)

# Create canvas items ONCE and store their IDs
        self.bg_item = self.canvas.create_image(0, 0, anchor='nw', image=self.bg_tk)
        self.player_item = self.canvas.create_image(CANVAS_SIZE//2, CANVAS_SIZE//2,
                                            anchor='center', image=self.player_tk)

# Safely call update_canvas
        self.update_canvas(idle)

# Handle window close
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

    def on_mousewheel(self, event):
        if event.num == 4 or event.delta > 0:
            self.zoom = min(self.zoom * 1.1, 4.0)
        elif event.num == 5 or event.delta < 0:
            self.zoom = max(self.zoom * 0.9, 0.5)
        self.update_canvas()

    def on_close(self):
    # Cancel scheduled callbacks so they don't fire after the window is closed
        if self._move_after_id is not None:
            self.root.after_cancel(self._move_after_id)
            self._move_after_id = None
        if self._anim_after_id is not None:
            self.root.after_cancel(self._anim_after_id)
            self._anim_after_id = None
        self.root.destroy()

    # ---------- File loading ----------
    def safe_open_rgba(self, path):
        try:
            return Image.open(path).convert("RGBA")
        except Exception:
            # transparent fallback so app still runs
            return Image.new("RGBA", (FRAME_SIZE, FRAME_SIZE), (0,0,0,0))

    def load_background(self):
        fp = filedialog.askopenfilename(filetypes=[("Image files","*.png;*.jpg;*.jpeg")])
        if fp:
            img = Image.open(fp).convert("RGBA")
            self.background = img.resize((BG_SIZE, BG_SIZE), Image.NEAREST)
            self.bg_scaled = self.background.resize((CANVAS_SIZE, CANVAS_SIZE), Image.NEAREST)
            self.update_canvas()

    def load_hat(self):
        fp = filedialog.askopenfilename(filetypes=[("PNG files","*.png")])
        if fp:
            self.hat_img = Image.open(fp).convert("RGBA")
            self.update_canvas()

    def load_head(self):
        fp = filedialog.askopenfilename(filetypes=[("PNG files","*.png")])
        if fp:
            self.head_img = Image.open(fp).convert("RGBA")
            self.update_canvas()

    def load_body(self):
        fp = filedialog.askopenfilename(filetypes=[("PNG files","*.png")])
        if fp:
            self.body_img = Image.open(fp).convert("RGBA")
            self.update_canvas()

    # ---------- Input handling ----------
    def on_key_press(self, event):
        k = event.keysym.lower()
        if k in ('w','a','s','d'):
            if k not in self.keys_down:
                self.keys_down.add(k)
                if len(self.key_queue) < MAX_KEYS_HELD:
                    self.key_queue.append(k)
            # start movement loop if not already running
            if self._move_after_id is None:
                self.move_loop()

    def on_key_release(self, event):
        k = event.keysym.lower()
        if k in self.keys_down:
            self.keys_down.remove(k)
        if not self.keys_down:
            # stop movement loop and snap to idle
            if self._move_after_id is not None:
                self.root.after_cancel(self._move_after_id)
                self._move_after_id = None
            self.update_canvas(self.get_combined_frame('idle', self.facing))
        # trim queue (anti-lag)
        self.key_queue = [kk for kk in self.key_queue if kk in self.keys_down][-MAX_KEYS_HELD:]

    def handle_action_key(self, key):
        # pause movement during actions
        if self._move_after_id is not None:
            self.root.after_cancel(self._move_after_id)
            self._move_after_id = None
        self.keys_down.clear()
        self.key_queue.clear()

        if key in ['i','j','k','l']:
            direction = {'i':'back','j':'left','k':'front','l':'right'}[key]
            self.facing = direction
            self.play_action(direction)
        elif key == 'g':
            self.play_grab(self.facing)
        elif key == 'h':
            self.play_damage(self.facing)
        elif key == 'f':
            # death frame immediate
            self.update_canvas(self.get_combined_frame('death', self.facing))

    # ---------- Movement loop (constant speed + diagonal normalize) ----------
    def move_loop(self):
        # compute desired movement vector from keys_down
        dx, dy = 0.0, 0.0
        kd = self.keys_down

        # pick display direction (diagonals map to left/right for walk frames)
        display_dir = self.facing
        if 'w' in kd and 'a' in kd:   display_dir = 'left'
        elif 's' in kd and 'a' in kd: display_dir = 'left'
        elif 'w' in kd and 'd' in kd: display_dir = 'right'
        elif 's' in kd and 'd' in kd: display_dir = 'right'
        elif 'w' in kd:               display_dir = 'back'
        elif 's' in kd:               display_dir = 'front'
        elif 'a' in kd:               display_dir = 'left'
        elif 'd' in kd:               display_dir = 'right'

        # raw vector (character moves => background scroll opposite sign we picked before)
        if 'w' in kd: dy += MOVE_SPEED     # up moves bg downward (positive offset)
        if 's' in kd: dy -= MOVE_SPEED
        if 'a' in kd: dx += MOVE_SPEED
        if 'd' in kd: dx -= MOVE_SPEED

        # normalize for diagonals to keep constant speed
        length = math.hypot(dx, dy)
        if length > 0:
            scale = MOVE_SPEED / length
            dx *= scale
            dy *= scale

            # boundaries (logical space)
            max_off = (CANVAS_SIZE // 2) - BORDER_MARGIN
            min_off = -max_off
            new_x = self.bg_offset_x + dx
            new_y = self.bg_offset_y + dy
            # clamp
            self.bg_offset_x = max(min(new_x, max_off), min_off)
            self.bg_offset_y = max(min(new_y, max_off), min_off)

            # advance walk frame
            self.walk_frame_idx = (self.walk_frame_idx + 1) % 5
            self.facing = display_dir
            frame = self.get_combined_frame('walk', display_dir, self.walk_frame_idx)
            self.update_canvas(frame)
        else:
            # no keys (safety)
            self.update_canvas(self.get_combined_frame('idle', self.facing))

        # reschedule if still moving
        if self.keys_down:
            self._move_after_id = self.root.after(TICK_MS, self.move_loop)
        else:
            self._move_after_id = None

    # ---------- Action/one-shot animations ----------
    def play_action(self, direction):
        total = 5 if direction == 'back' else 4
        def step(i=0):
            if i >= total:
                self.update_canvas(self.get_combined_frame('idle', direction))
                return
            self.update_canvas(self.get_combined_frame('action', direction, i))
            self._anim_after_id = self.root.after(ANIMATION_DELAY_MS, lambda: step(i+1))
        step()

    def play_grab(self, direction):
        def step(i=0):
            if i > 0:
                self.update_canvas(self.get_combined_frame('idle', direction))
                return
            self.update_canvas(self.get_combined_frame('grab', direction))
            self._anim_after_id = self.root.after(ANIMATION_DELAY_MS, lambda: step(i+1))
        step()

    def play_damage(self, direction):
        def step(i=0):
            if i > 0:
                self.update_canvas(self.get_combined_frame('idle', direction))
                return
            self.update_canvas(self.get_combined_frame('damage', direction))
            self._anim_after_id = self.root.after(ANIMATION_DELAY_MS, lambda: step(i+1))
        step()

    # ---------- Sprite composition (your original logic) ----------
    def get_combined_frame(self, action, direction, frame_index=0):
        if self.head_img is None or self.body_img is None:
            return Image.new("RGBA", (FRAME_SIZE*SCALE_FACTOR, (FRAME_SIZE+BODY_OFFSET_Y)*SCALE_FACTOR), (0,0,0,0))

        # --- HEAD ---
        if action in HEAD_FRAME_POSITIONS:
            hy = HEAD_FRAME_POSITIONS[action][direction]
        else:
            hy = HEAD_FRAME_POSITIONS['idle'][direction]

        head_crop = self.head_img.crop((0, hy, 32, hy+32))

# --- HAT ---
        if action in HAT_FRAME_POSITIONS:
            hx, hy = HAT_FRAME_POSITIONS[action][direction]
        else:
            hx, hy = HAT_FRAME_POSITIONS['idle'][direction]

        hat_crop = self.hat_img.crop((hx, hy, hx+HAT_FRAME_SIZE, hy+HAT_FRAME_SIZE))
        hat_x_offset = -(HAT_FRAME_SIZE - FRAME_SIZE) // 2  # center 48px hat over 32px head

        # BODY
        if action == 'damage':
            bx, by = BODY_DAMAGE_COORDS[direction]   # for damage
            body_crop = self.body_img.crop((bx, by, bx+FRAME_SIZE, by+FRAME_SIZE))
        elif action == 'death':
            bx, by = BODY_DEATH_COORDS[direction]    # for death
            body_crop = self.body_img.crop((bx, by, bx+48, by+32))  # 48x32
        elif action == 'grab':
            vx = {'back':0, 'left':32, 'front':64, 'right':96}[direction]
            body_crop = self.body_img.crop((vx, 416, vx+FRAME_SIZE, 416+FRAME_SIZE))
        elif action == 'action':
            vx = {'back':0, 'left':32, 'front':64, 'right':96}[direction]
            by = 160 + frame_index * FRAME_SIZE
            body_crop = self.body_img.crop((vx, by, vx+FRAME_SIZE, by+FRAME_SIZE))
        elif action == 'walk':
            vx = {'back':0, 'left':32, 'front':64, 'right':96}[direction]
            by = FRAME_SIZE + frame_index * FRAME_SIZE  # 32 + i*32
            body_crop = self.body_img.crop((vx, by, vx+FRAME_SIZE, by+FRAME_SIZE))
        else:
            vx = {'back':0, 'left':32, 'front':64, 'right':96}[direction]
            body_crop = self.body_img.crop((vx, 0, vx+FRAME_SIZE, 0+FRAME_SIZE))

        # Composite (allow head bob during walk)
        width = FRAME_SIZE
        height = FRAME_SIZE + BODY_OFFSET_Y
        composite = Image.new("RGBA", (width, height), (0,0,0,0))

        head_y_offset = HEAD_BOB_OFFSETS[frame_index] if action == 'walk' else 0
        hat_y_offset = HAT_BOB_OFFSETS[frame_index] if action == 'walk' else 0
        if action == 'death':
            composite.paste(body_crop, (0, BODY_OFFSET_Y), body_crop)
            composite.paste(head_crop, (16, 12), head_crop)
            composite.paste(hat_crop, (16 + hat_x_offset, 12 + HAT_OFFSET_Y), hat_crop)
        else:
            composite.paste(body_crop, (0, BODY_OFFSET_Y), body_crop)
            composite.paste(head_crop, (0, head_y_offset), head_crop)
            composite.paste(hat_crop, (hat_x_offset, hat_y_offset + HAT_OFFSET_Y), hat_crop)
        return composite.resize((width*SCALE_FACTOR, height*SCALE_FACTOR), Image.NEAREST)
    
    # ---------- Canvas drawing ----------
    def update_canvas(self, player_frame=None):
        if player_frame is None:
            player_frame = self.get_combined_frame('idle', self.facing)

    # --- Scale background with zoom ---
        bg_w = int(self.bg_scaled.width * self.zoom)
        bg_h = int(self.bg_scaled.height * self.zoom)
        bg_zoomed = self.bg_scaled.resize((bg_w, bg_h), Image.NEAREST)

    # --- Scale player with zoom ---
        pw = int(player_frame.width * self.zoom)
        ph = int(player_frame.height * self.zoom)
        player_zoomed = player_frame.resize((pw, ph), Image.NEAREST)

    # Rebuild PhotoImages
        self.bg_tk = ImageTk.PhotoImage(bg_zoomed, master=self.canvas)
        self.player_tk = ImageTk.PhotoImage(player_zoomed, master=self.canvas)

    # Update canvas items (reuse existing items)
        self.canvas.itemconfigure(self.bg_item, image=self.bg_tk)
        self.canvas.itemconfigure(self.player_item, image=self.player_tk)

    # --- Position background by CENTER so zoom pivots around the player ---
    # world -> screen: scale offsets by zoom, then center
        bg_cx = CANVAS_SIZE // 2 + int(self.bg_offset_x * self.zoom)
        bg_cy = CANVAS_SIZE // 2 + int(self.bg_offset_y * self.zoom)
        bg_x  = int(bg_cx - bg_w / 2)
        bg_y  = int(bg_cy - bg_h / 2)

        self.canvas.coords(self.bg_item, bg_x, bg_y)
        self.canvas.coords(self.player_item, CANVAS_SIZE // 2, CANVAS_SIZE // 2)

        self.canvas.update_idletasks()

# --- Run the App ---
if __name__ == "__main__":
    root = tk.Tk()
    app = SpriteViewerApp(root)
    root.mainloop()
