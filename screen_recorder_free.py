# -*- coding: utf-8 -*-
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import numpy as np
import pyautogui
import cv2
import threading
import time
import os
import sys
import json
import subprocess
import sqlite3
import hashlib
import uuid
from datetime import datetime, timedelta
from PIL import Image, ImageTk
import requests
import webbrowser

# 尝试导入imageio_ffmpeg用于快速视频裁剪
try:
    import imageio_ffmpeg
    IMAGEIO_FFMPEG_AVAILABLE = True
except ImportError:
    IMAGEIO_FFMPEG_AVAILABLE = False

# 尝试导入watchdog库用于文件系统监控
try:
    from watchdog.observers import Observer
    from watchdog.events import FileSystemEventHandler
    WATCHDOG_AVAILABLE = True
    
    class FileSystemMonitor(FileSystemEventHandler):
        """文件系统监控类"""
        def __init__(self, screen_recorder):
            self.screen_recorder = screen_recorder
        
        def on_any_event(self, event):
            """当文件系统发生任何变化时调用"""
            # 只处理视频资料库目录的变化
            if os.path.exists(self.screen_recorder.video_library_dir) and self.screen_recorder.video_library_dir in event.src_path:
                # 延迟更新，避免频繁触发
                self.screen_recorder.root.after(500, self.screen_recorder.init_folder_structure)
except ImportError:
    WATCHDOG_AVAILABLE = False
    print("watchdog库未安装，文件系统监控功能将不可用")
    
    class FileSystemMonitor:
        """文件系统监控类（空实现）"""
        def __init__(self, screen_recorder):
            self.screen_recorder = screen_recorder
        
        def on_any_event(self, event):
            pass

def set_window_icon(root):
    """设置窗口图标（任务栏显示）"""
    try:
        # 判断是否为 PyInstaller 打包环境
        if hasattr(sys, '_MEIPASS'):
            # 打包后：从临时目录加载
            icon_path = os.path.join(sys._MEIPASS, 'app_icon.ico')
        else:
            # 开发环境：从当前目录加载
            icon_path = os.path.join(os.path.dirname(__file__), 'app_icon.ico')
            
        if os.path.exists(icon_path):
            # 使用 PIL 加载图标并设置
            icon_image = Image.open(icon_path)
            icon_photo = ImageTk.PhotoImage(icon_image)
            root.iconphoto(True, icon_photo)
            # 保留引用防止被垃圾回收
            root.icon_image = icon_photo
        else:
            print(f"图标文件不存在: {icon_path}")
    except Exception as e:
        print(f"设置窗口图标失败: {str(e)}")

class ScreenRecorder:
    def __init__(self, root):
        self.root = root
        self.root.title("直播录屏标记助手")
        
        # 设置窗口图标（任务栏显示）
        set_window_icon(self.root)

        # 获取屏幕大小的80%
        screen_width = root.winfo_screenwidth()
        screen_height = root.winfo_screenheight()
        window_width = int(screen_width * 0.8)
        window_height = int(screen_height * 0.8)
        # 设置窗口大小
        self.root.geometry(f"{window_width}x{window_height}")
        self.root.resizable(True, True)
        self.recording = False
        self.paused = False
        self.recorder = None
        self.video_file = None
        self.markers = []
        self.marker_count = 0
        self.clips = []
        self.clip_start = None
        self.video_duration = 0
        self.current_time = 0
        self.update_thread = None
        self.stop_update = False
        self.recorded_frames = 0
        self.x = 0
        self.y = 0
        self.width = 1920
        self.height = 1080
        self.recording_start_time = 0
        self.dragging = False
        self.drag_start_x = 0
        self.drag_start_y = 0
        self.video_capture = None
        self.video_playing = False
        self.video_thread = None
        self.stop_video = False
        self.video_paused = False
        self.recordings_file = "recordings.txt"
        self.progress_knob_id = None
        self.progress_bar_dragging = False
        self.video_lock = threading.Lock()  # 视频操作锁，防止多线程冲突
        
        # 用户账号相关变量
        self.is_logged_in = False  # 用户登录状态
        self.current_user = None  # 当前用户信息
        
        # 存储每个视频文件对应的标记列表
        self.video_markers = {}
        
        # 存储每个视频文件对应的片段列表
        self.video_clips = {}
        
        # 截取视频相关变量
        self.clip_mode = False
        self.clip_start = 0
        self.clip_end = 0
        self.clip_start_id = None
        self.clip_end_id = None
        self.clip_area_id = None
        self.dragging_clip_start = False
        self.dragging_clip_end = False
        
        # 缩略功能区相关属性
        self.mini_window = None
        self.mini_pause_btn = None
        self.mini_stop_btn = None
        self.mini_mark_btn = None
        self.mini_status_label = None
        
        # 目录相关变量 - 使用用户文档目录确保权限
        user_documents = os.path.expanduser("~/Documents")
        self.app_data_dir = os.path.join(user_documents, "LiveRecorder")  # 应用数据根目录
        self.recordings_dir = os.path.join(self.app_data_dir, "recordings")  # 录制目录
        self.current_session_dir = None  # 当前录制会话目录
        self.clip_dir = "截取视频"  # 截取视频文件夹
        self.video_library_dir = os.path.join(self.app_data_dir, "视频资料库")  # 独立的视频资料库目录
        
        # 确保目录存在
        self.ensure_directories()

        self.create_ui()
        
        # 显示保存位置提示
        print("=" * 60)
        print(f"[启动] 应用数据目录: {self.app_data_dir}")
        print(f"[启动] 录制保存目录: {self.recordings_dir}")
        print("=" * 60)
        
        # 启动文件系统监控
        self.start_file_monitor()
    
    def ensure_directories(self):
        """确保必要的目录存在 - 使用用户文档目录确保权限"""
        try:
            # 确保应用数据根目录存在
            if not os.path.exists(self.app_data_dir):
                os.makedirs(self.app_data_dir)
                print(f"[目录] 创建应用数据目录: {self.app_data_dir}")
            
            # 确保recordings目录存在
            if not os.path.exists(self.recordings_dir):
                os.makedirs(self.recordings_dir)
                print(f"[目录] 创建录制目录: {self.recordings_dir}")
            
            # 确保视频资料库目录存在
            if not os.path.exists(self.video_library_dir):
                os.makedirs(self.video_library_dir)
                print(f"[目录] 创建视频资料库: {self.video_library_dir}")
                
        except Exception as e:
            print(f"[错误] 创建目录失败: {e}")
            print(f"[信息] 尝试使用临时目录作为备用")
            import tempfile
            self.app_data_dir = os.path.join(tempfile.gettempdir(), "LiveRecorder")
            self.recordings_dir = os.path.join(self.app_data_dir, "recordings")
            self.video_library_dir = os.path.join(self.app_data_dir, "视频资料库")
            if not os.path.exists(self.recordings_dir):
                os.makedirs(self.recordings_dir)
            if not os.path.exists(self.video_library_dir):
                os.makedirs(self.video_library_dir)
            print(f"[备用] 使用临时目录: {self.app_data_dir}")
    
    def start_file_monitor(self):
        """启动文件系统监控"""
        if WATCHDOG_AVAILABLE and os.path.exists(self.video_library_dir):
            self.file_observer = Observer()
            event_handler = FileSystemMonitor(self)
            # 监控视频资料库目录的所有子目录
            self.file_observer.schedule(event_handler, self.video_library_dir, recursive=True)
            self.file_observer.start()
            print("文件系统监控已启动")
    
    def stop_file_monitor(self):
        """停止文件系统监控"""
        if WATCHDOG_AVAILABLE and self.file_observer:
            self.file_observer.stop()
            self.file_observer.join()
            print("文件系统监控已停止")
    
    def create_ui(self):
        # 设置现代主题 - 剪映专业风格
        self.style = ttk.Style()
        self.style.theme_use('clam')
        
        # 主色调定义 - Trae黑色主题配绿色点缀
        self.bg_color = "#1a1a1a"           # 深黑色背景
        self.card_bg = "#252525"            # 深灰色卡片背景
        self.light_bg = "#333333"           # 浅色背景
        self.text_color = "#ffffff"          # 主文本颜色
        self.secondary_text = "#b0b0b0"      # 次要文本颜色
        self.accent_color = "#34a853"        # 强调色（Trae绿）
        self.accent_hover = "#2d9249"       # 悬停色
        self.success_color = "#34a853"        # 成功色
        self.danger_color = "#ea4335"        # 危险色
        self.border_color = "#404040"        # 边框色
        self.input_bg = "#2d2d2d"            # 输入框背景
        
        # 配置主窗口
        self.root.configure(bg=self.bg_color)
        # 使用更现代的字体
        self.root.option_add('*Font', ('Segoe UI', 9))
        
        # 配置样式
        # 框架样式
        self.style.configure('Custom.TFrame', background=self.bg_color)
        self.style.configure('Card.TFrame', background=self.card_bg)
        self.style.configure('Light.TFrame', background=self.light_bg)
        
        # LabelFrame样式
        self.style.configure('Custom.TLabelframe', background=self.card_bg,
                           borderwidth=1, relief='solid', bordercolor=self.border_color)
        self.style.configure('Custom.TLabelframe.Label', background=self.card_bg,
                           foreground=self.secondary_text, font=('Segoe UI', 10, 'bold'))
        
        # Label样式
        self.style.configure('Custom.TLabel', background=self.bg_color,
                          foreground=self.text_color, font=('Segoe UI', 9))
        self.style.configure('Title.TLabel', background=self.card_bg,
                          foreground=self.text_color, font=('Segoe UI', 12, 'bold'))
        self.style.configure('Small.TLabel', background=self.card_bg,
                          foreground=self.secondary_text, font=('Segoe UI', 9))
        
        # 按钮基础样式 - 现代圆角设计
        self.style.configure('Custom.TButton',
                          background=self.light_bg,
                          foreground=self.text_color,
                          font=('Segoe UI', 9, 'bold'),
                          padding=(16, 10),
                          borderwidth=0,
                          relief='flat',
                          focuscolor='none',
                          borderradius=6)  # 圆角
        self.style.map('Custom.TButton',
                    background=[('active', '#4a4a4a'), ('pressed', '#3a3a3a'), ('disabled', '#3a3a3a')],
                    foreground=[('active', self.text_color), ('disabled', '#666666')])
        
        # 强调按钮样式 - 绿色圆角
        self.style.configure('Accent.TButton',
                          background=self.accent_color,
                          foreground='#ffffff',
                          font=('Segoe UI', 9, 'bold'),
                          padding=(16, 10),
                          borderwidth=0,
                          relief='flat',
                          focuscolor='none',
                          borderradius=6)  # 圆角
        self.style.map('Accent.TButton',
                    background=[('active', self.accent_hover), ('pressed', '#267340'), ('disabled', '#3a3a3a')],
                    foreground=[('active', '#ffffff'), ('disabled', '#666666')])
        
        # 危险按钮样式 - 红色圆角
        self.style.configure('Danger.TButton',
                          background=self.danger_color,
                          foreground='#ffffff',
                          font=('Segoe UI', 9, 'bold'),
                          padding=(16, 10),
                          borderwidth=0,
                          relief='flat',
                          focuscolor='none',
                          borderradius=6)  # 圆角
        self.style.map('Danger.TButton',
                    background=[('active', '#ff6b5b'), ('pressed', '#c5221f')],
                    foreground=[('active', '#ffffff')])
        
        # 输入框样式 - 圆角设计
        self.style.configure('Custom.TEntry',
                          fieldbackground=self.input_bg,
                          foreground=self.text_color,
                          background=self.light_bg,
                          borderwidth=1,
                          relief='solid',
                          bordercolor=self.border_color,
                          padding=8,
                          borderradius=4)  # 圆角
        self.style.map('Custom.TEntry',
                    fieldbackground=[('focus', self.input_bg)],
                    bordercolor=[('focus', self.accent_color)])
        
        # 控制栏 - 现代化卡片式设计
        self.control_frame = tk.Frame(self.root, bg=self.card_bg, padx=24, pady=20)
        self.control_frame.pack(fill=tk.X, side=tk.TOP, pady=(10, 10), padx=10)
        # 添加圆角效果（通过模拟实现）
        self.control_frame.configure(relief='flat')
        
        # 标题区域
        title_frame = tk.Frame(self.control_frame, bg=self.card_bg)
        title_frame.pack(side=tk.LEFT, fill=tk.Y, expand=True)
        
        # 标题和使用流程的垂直容器
        title_content_frame = tk.Frame(title_frame, bg=self.card_bg)
        title_content_frame.pack(side=tk.LEFT, anchor=tk.CENTER, fill=tk.Y)
        
        title_label = tk.Label(title_content_frame, text="直播录屏标记助手",
                font=('STKaiti', 18, 'bold'),
                bg=self.card_bg, fg='#2ecc71')
        title_label.pack(side=tk.TOP, anchor=tk.W)
        
        # 使用流程说明
        instruction_label = tk.Label(title_content_frame, 
                text="使用流程:工具以外打开直播画面 → 开始录屏 → 标记进度 → 结束录屏 → 找到标记进度黄色标记截取需要的视频片段",
                font=('Segoe UI', 9),
                bg=self.card_bg, fg=self.secondary_text)
        instruction_label.pack(side=tk.TOP, anchor=tk.W, fill=tk.X, pady=(8, 0))
        
        # 按钮区域
        self.button_frame = tk.Frame(self.control_frame, bg=self.card_bg)
        self.button_frame.pack(side=tk.RIGHT, fill=tk.Y)
        
        # 主按钮 - 使用grid布局固定位置
        self.start_btn = ttk.Button(self.button_frame, text="开始录屏", command=self.start_recording, 
                                  style='Accent.TButton')
        self.start_btn.grid(row=0, column=0, padx=8, pady=4)
        
        self.pause_btn = ttk.Button(self.button_frame, text="暂停录屏", command=self.pause_recording, 
                                  style='Custom.TButton', takefocus=False)
        # 初始状态隐藏
        
        self.stop_btn = ttk.Button(self.button_frame, text="结束录屏", command=self.stop_recording, 
                                  style='Danger.TButton')
        # 初始状态隐藏
        
        self.mark_btn = ttk.Button(self.button_frame, text="标记进度[空格]", command=self.mark_progress, 
                                  style='Accent.TButton', takefocus=False)
        self.mark_btn.grid(row=0, column=2, padx=6, pady=2)

        # 添加分隔符（column=3）
        separator = ttk.Separator(self.button_frame, orient=tk.VERTICAL)
        separator.grid(row=0, column=3, padx=12, pady=4, sticky='ns')
        
        self.clip_btn = ttk.Button(self.button_frame, text="截取视频", command=self.start_clip, 
                                  state=tk.DISABLED, style='Custom.TButton')
        self.clip_btn.grid(row=0, column=4, padx=8, pady=4)
        
        self.finish_clip_btn = ttk.Button(self.button_frame, text="完成截取", command=self.finish_clip, 
                                         state=tk.DISABLED, style='Accent.TButton')
        self.finish_clip_btn.grid(row=0, column=5, padx=8, pady=4)

        # 录制记录按钮
        self.record_history_btn = ttk.Button(self.button_frame, text="录制记录", command=self.show_record_history, 
                                           style='Custom.TButton')
        self.record_history_btn.grid(row=0, column=6, padx=8, pady=4)
        
        # 视频资料库按钮
        self.video_library_btn = ttk.Button(self.button_frame, text="视频资料库", command=self.show_video_library, 
                                           style='Custom.TButton')
        self.video_library_btn.grid(row=0, column=7, padx=8, pady=4)

        # 主框架 - 左侧导航 + 右侧内容
        self.root_container = tk.Frame(self.root, bg=self.bg_color)
        self.root_container.pack(fill=tk.BOTH, expand=True)

        # 左侧导航框架
        self.nav_frame = tk.Frame(self.root_container, bg=self.card_bg, width=150)
        self.nav_frame.pack(side=tk.LEFT, fill=tk.Y, padx=(10, 0), pady=10)
        self.nav_frame.pack_propagate(False)

        # 导航按钮样式
        nav_btn_style = {
            'font': ('Segoe UI', 10),
            'bg': self.card_bg,
            'fg': self.secondary_text,
            'activebackground': self.accent_color,
            'activeforeground': '#ffffff',
            'relief': 'flat',
            'anchor': 'w',
            'padx': 15,
            'pady': 12,
            'cursor': 'hand2'
        }

        # 导航按钮
        self.nav_buttons = {}
        nav_items = [
            ('home', '🏠 首页'),
            ('tutorial', '📖 使用教程'),
            ('service', '📞 联系客服'),
            ('about', 'ℹ️ 关于')
        ]

        for idx, (btn_id, btn_text) in enumerate(nav_items):
            btn = tk.Label(self.nav_frame, text=btn_text, **nav_btn_style)
            btn.pack(fill=tk.X, pady=1)
            btn.bind('<Button-1>', lambda e, bid=btn_id: self.switch_tab(bid))
            self.nav_buttons[btn_id] = btn

        # 当前tab
        self.current_tab = 'home'
        self.highlight_nav(self.current_tab)

        # 右侧内容区域容器
        self.content_container = tk.Frame(self.root_container, bg=self.bg_color)
        self.content_container.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=10, pady=10)

        # 创建5个tab页面
        self.tab_pages = {}
        for tab_id in ['home', 'vip', 'tutorial', 'service', 'about']:
            page = tk.Frame(self.content_container, bg=self.bg_color)
            page.pack(fill=tk.BOTH, expand=True)
            self.tab_pages[tab_id] = page

        # 首页内容（原有主页内容）
        self.create_home_tab()

        # 其他tab内容初始化
        self.create_tutorial_tab()
        self.create_service_tab()
        self.create_about_tab()

        # 默认显示首页
        self.show_tab('home')

    def create_tutorial_tab(self):
        """创建使用教程tab"""
        page = self.tab_pages['tutorial']
        
        # 标题
        title = tk.Label(page, text="📖 使用教程",
                        font=('Arial', 18, 'bold'),
                        bg=self.bg_color, fg=self.accent_color)
        title.pack(anchor=tk.W, pady=(20, 20), padx=20)
        
        # 教程步骤
        steps = [
            ("1", "准备直播画面", "打开需要录制的直播页面或软件"),
            ("2", "开始录屏", "点击「开始录屏」按钮，工具将开始录制屏幕内容"),
            ("3", "标记进度", "在直播过程中，点击「标记进度」或按空格键添加标记点"),
            ("4", "结束录屏", "直播结束后，点击「结束录屏」停止录制"),
            ("5", "截取视频", "在进度条上拖拽选择起止点，点击「截取视频」生成片段"),
            ("6", "保存分享", "生成的视频片段保存在recordings文件夹中，可随时查看")
        ]
        
        for num, step_title, step_desc in steps:
            step_frame = tk.Frame(page, bg=self.card_bg, padx=20, pady=15)
            step_frame.pack(fill=tk.X, padx=20, pady=(0, 10))
            
            num_label = tk.Label(step_frame, text=num,
                               font=('Arial', 16, 'bold'),
                               bg=self.accent_color, fg='#ffffff',
                               width=3, height=1)
            num_label.pack(side=tk.LEFT, padx=(0, 15))
            
            content_frame = tk.Frame(step_frame, bg=self.card_bg)
            content_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)
            
            step_title_label = tk.Label(content_frame, text=step_title,
                                       font=('Arial', 12, 'bold'),
                                       bg=self.card_bg, fg=self.text_color)
            step_title_label.pack(anchor=tk.W)
            
            step_desc_label = tk.Label(content_frame, text=step_desc,
                                      font=('Arial', 10),
                                      bg=self.card_bg, fg=self.secondary_text)
            step_desc_label.pack(anchor=tk.W, pady=(5, 0))

    def create_service_tab(self):
        """创建联系客服tab"""
        page = self.tab_pages['service']
        
        # 标题
        title = tk.Label(page, text="📞 联系客服",
                        font=('Arial', 18, 'bold'),
                        bg=self.bg_color, fg=self.accent_color)
        title.pack(anchor=tk.W, pady=(20, 20), padx=20)
        
        # 联系信息卡片
        info_card = tk.Frame(page, bg=self.card_bg, padx=30, pady=30)
        info_card.pack(fill=tk.BOTH, expand=True, padx=20)

        # 客服邮箱（硬编码）
        email_value = '2501103849@qq.com'
        email_frame = tk.Frame(info_card, bg=self.card_bg)
        email_frame.pack(fill=tk.X, pady=(0, 20))

        tk.Label(email_frame, text="客服邮箱：",
                font=('Arial', 12),
                bg=self.card_bg, fg=self.text_color).pack(side=tk.LEFT)

        self.service_email_label = tk.Label(email_frame, text=email_value,
                font=('Arial', 12),
                bg=self.card_bg, fg=self.text_color)
        self.service_email_label.pack(side=tk.LEFT)

        # 工作时间（硬编码）
        time_value = '周一至周五 9:00-18:00'
        time_frame = tk.Frame(info_card, bg=self.card_bg)
        time_frame.pack(fill=tk.X)
        
        tk.Label(time_frame, text="工作时间：",
                font=('Arial', 12),
                bg=self.card_bg, fg=self.text_color).pack(side=tk.LEFT)
        
        self.service_time_label = tk.Label(time_frame, text=time_value,
                font=('Arial', 12),
                bg=self.card_bg, fg=self.text_color)
        self.service_time_label.pack(side=tk.LEFT)
        
        # 提示
        tip_label = tk.Label(page, text="* 遇到问题可通过以上方式联系我们",
                           font=('Arial', 9),
                           bg=self.bg_color, fg=self.secondary_text,
                           pady=20)
        tip_label.pack()

    def create_about_tab(self):
        """创建关于软件tab"""
        page = self.tab_pages['about']
        
        # 标题
        title = tk.Label(page, text="ℹ️ 关于软件",
                        font=('Arial', 18, 'bold'),
                        bg=self.bg_color, fg=self.accent_color)
        title.pack(anchor=tk.W, pady=(20, 20), padx=20)
        
        # 关于信息卡片
        about_card = tk.Frame(page, bg=self.card_bg, padx=30, pady=30)
        about_card.pack(fill=tk.BOTH, expand=True, padx=20)
        
        # 软件名称
        name_label = tk.Label(about_card, text="直播录屏标记助手",
                             font=('Arial', 16, 'bold'),
                             bg=self.card_bg, fg=self.accent_color)
        name_label.pack(pady=(0, 10))
        
        # 版本号
        version_label = tk.Label(about_card, text="版本：v1.0.0",
                                font=('Arial', 11),
                                bg=self.card_bg, fg=self.text_color)
        version_label.pack()
        
        # 法律声明和用户协议区域
        link_frame = tk.Frame(about_card, bg=self.card_bg)
        link_frame.pack(pady=20)
        
        # 法律声明（超链接样式）
        legal_label = tk.Label(link_frame, text="法律声明", 
                              font=('Arial', 10, 'underline'),
                              bg=self.card_bg, fg=self.text_color,
                              cursor='hand2')
        legal_label.pack(side=tk.LEFT, padx=15)
        legal_label.bind('<Button-1>', lambda e: self.open_legal_notice())
        
        # 分隔符
        sep_label = tk.Label(link_frame, text="|", 
                           font=('Arial', 10),
                           bg=self.card_bg, fg=self.secondary_text)
        sep_label.pack(side=tk.LEFT, padx=5)
        
        # 用户协议（超链接样式）
        agreement_label = tk.Label(link_frame, text="用户协议", 
                                  font=('Arial', 10, 'underline'),
                                  bg=self.card_bg, fg=self.text_color,
                                  cursor='hand2')
        agreement_label.pack(side=tk.LEFT, padx=15)
        agreement_label.bind('<Button-1>', lambda e: self.open_user_agreement())
        
        # 版权信息
        copyright_label = tk.Label(page,
                                 text="© 2024 直播录屏标记助手 版权所有",
                                 font=('Arial', 9),
                                 bg=self.bg_color, fg=self.secondary_text,
                                 pady=20)
        copyright_label.pack()

    def open_legal_notice(self):
        """打开法律声明"""
        webbrowser.open('https://Wadeonetest.github.io/Wadeonetest-zbtip-zbtipfree/legal.html')

    def open_user_agreement(self):
        """打开用户协议"""
        webbrowser.open('https://Wadeonetest.github.io/Wadeonetest-zbtip-zbtipfree/terms.html')

    def highlight_nav(self, tab_id):
        """高亮导航按钮"""
        for btn_id, btn in self.nav_buttons.items():
            if btn_id == tab_id:
                btn.config(bg=self.accent_color, fg='#ffffff')
            else:
                btn.config(bg=self.card_bg, fg=self.secondary_text)

    def switch_tab(self, tab_id):
        """切换tab"""
        self.current_tab = tab_id
        self.highlight_nav(tab_id)
        self.show_tab(tab_id)

    def show_tab(self, tab_id):
        """显示指定tab"""
        for tid, page in self.tab_pages.items():
            if tid == tab_id:
                page.pack(fill=tk.BOTH, expand=True)
            else:
                page.pack_forget()

    def create_home_tab(self):
        """创建首页tab"""
        page = self.tab_pages['home']
        
        # 主框架
        self.main_frame = tk.Frame(page, bg=self.bg_color)
        self.main_frame.pack(fill=tk.BOTH, expand=True)
        
        # 左侧框架
        self.left_frame = tk.Frame(self.main_frame, bg=self.bg_color)
        self.left_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 16))
        
        # 右侧面板宽度
        self.right_panel_width = 200
        
        # 右侧视频片段面板 - 现代化设计
        self.right_frame = ttk.LabelFrame(self.main_frame, text="视频片段", padding=16, style='Custom.TLabelframe')
        self.right_frame.pack(side=tk.RIGHT, fill=tk.Y, padx=(10, 10), pady=10)
        self.right_frame.configure(width=self.right_panel_width)
        
        # 视频资料库面板 - 现代化设计
        self.library_frame = ttk.LabelFrame(self.main_frame, text="视频资料库", padding=16, style='Custom.TLabelframe')
        self.library_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(10, 10), pady=10)
        self.library_frame.pack_forget()  # 初始隐藏
        
        # 视频资料库搜索框
        search_frame = tk.Frame(self.library_frame, bg=self.card_bg)
        search_frame.pack(fill=tk.X, pady=(0, 10))
        
        self.library_search_var = tk.StringVar()
        self.library_search_entry = ttk.Entry(search_frame, textvariable=self.library_search_var, style='Custom.TEntry')
        self.library_search_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 10))
        self.library_search_entry.bind("<FocusIn>", self.show_folder_structure)
        self.library_search_entry.bind("<KeyRelease>", self.search_files)
        
        ttk.Button(search_frame, text="搜索", command=self.search_files, style='Custom.TButton').pack(side=tk.RIGHT)
        
        # 创建文件夹和文件图标
        # 文件夹图标（黄色文件夹形状）
        folder_img = Image.new('RGBA', (16, 16), (255, 255, 255, 0))
        folder_data = folder_img.load()
        # 绘制文件夹主体
        for x in range(16):
            for y in range(16):
                if y >= 8:
                    # 文件夹底部
                    folder_data[x, y] = (255, 168, 32, 255)  # 黄色
                else:
                    # 文件夹顶部
                    if x > y + 4:
                        folder_data[x, y] = (255, 168, 32, 255)  # 黄色
        # 绘制文件夹细节
        for x in range(4, 12):
            for y in range(10, 14):
                folder_data[x, y] = (255, 203, 52, 255)  # 浅黄色
        self.folder_icon = ImageTk.PhotoImage(folder_img)
        
        # 文件图标（绿色实心方格）
        file_img = Image.new('RGB', (16, 16), color='#4CAF50')
        self.file_icon = ImageTk.PhotoImage(file_img)
        
        # 文件夹树状结构
        self.folder_tree = ttk.Treeview(self.library_frame, style='Custom.Treeview')
        self.folder_tree.pack(fill=tk.BOTH, expand=True, pady=(0, 10))
        self.folder_tree.bind("<Double-1>", self.open_selected_folder)
        
        # 添加高亮样式
        self.folder_tree.tag_configure('highlight', background='#34a853', foreground='#ffffff')
        
        # 搜索结果统计标签
        self.search_stats_label = tk.Label(self.library_frame, text="", 
                                         bg=self.card_bg, 
                                         fg=self.secondary_text, 
                                         font=('Segoe UI', 8))
        self.search_stats_label.pack(fill=tk.X, pady=(0, 10))
        
        # 资料库控制按钮
        library_buttons = tk.Frame(self.library_frame, bg=self.card_bg)
        library_buttons.pack(fill=tk.X, pady=(0, 10))
        
        ttk.Button(library_buttons, text="打开", command=self.open_current_folder, style='Custom.TButton').pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(library_buttons, text="新建文件夹", command=self.create_new_folder, style='Custom.TButton').pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(library_buttons, text="导入文件", command=self.import_file, style='Custom.TButton').pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(library_buttons, text="重命名", command=self.rename_selected_item, style='Custom.TButton').pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(library_buttons, text="删除", command=self.delete_selected_item, style='Danger.TButton').pack(side=tk.LEFT)
        

        
        # 视频预览 - 现代化卡片式设计
        self.video_frame = ttk.LabelFrame(self.left_frame, text="视频预览", padding=16, style='Custom.TLabelframe')
        self.video_frame.pack(fill=tk.BOTH, expand=True, pady=(10, 10), padx=10)
        
        # 视频文件名区域框架
        filename_frame = tk.Frame(self.video_frame, bg=self.card_bg)
        filename_frame.pack(side=tk.TOP, anchor=tk.W, pady=(0, 8), fill=tk.X)
        
        # 视频文件名标签
        self.video_filename_label = tk.Label(filename_frame, text="", 
                                           font=('Arial', 10),
                                           bg=self.card_bg, fg="#999999")
        self.video_filename_label.pack(side=tk.LEFT, anchor=tk.W)
        
        # 修改文件名按钮
        self.rename_btn = tk.Button(filename_frame, text="✏️", command=self.rename_video_file,
                                   font=('Segoe UI Emoji', 11), bg=self.light_bg, fg="#ffffff",
                                   relief=tk.FLAT, cursor='hand2', bd=0,
                                   highlightthickness=0,
                                   padx=6, pady=2)
        self.rename_btn.pack(side=tk.LEFT, padx=(10, 0))
        self.rename_btn.pack_forget()  # 初始隐藏
        
        # 文件位置按钮
        self.location_btn = tk.Button(filename_frame, text="📁", command=self.open_video_location,
                                   font=('Segoe UI Emoji', 11), bg=self.light_bg, fg="#ffffff",
                                   relief=tk.FLAT, cursor='hand2', bd=0,
                                   highlightthickness=0,
                                   padx=6, pady=2)
        self.location_btn.pack(side=tk.LEFT, padx=(10, 0))
        self.location_btn.pack_forget()  # 初始隐藏
        
        # 添加按钮悬停效果
        def on_rename_enter(e):
            # 平滑过渡到悬停颜色
            for i in range(10):
                alpha = i / 10
                bg_color = f"#{int((1-alpha)*int(self.light_bg[1:3], 16) + alpha*int(self.accent_color[1:3], 16)):02x}{int((1-alpha)*int(self.light_bg[3:5], 16) + alpha*int(self.accent_color[3:5], 16)):02x}{int((1-alpha)*int(self.light_bg[5:7], 16) + alpha*int(self.accent_color[5:7], 16)):02x}"
                self.rename_btn.config(bg=bg_color)
                self.root.update()
                self.root.after(10)
        def on_rename_leave(e):
            # 平滑过渡到原始颜色
            for i in range(10):
                alpha = i / 10
                bg_color = f"#{int(alpha*int(self.light_bg[1:3], 16) + (1-alpha)*int(self.accent_color[1:3], 16)):02x}{int(alpha*int(self.light_bg[3:5], 16) + (1-alpha)*int(self.accent_color[3:5], 16)):02x}{int(alpha*int(self.light_bg[5:7], 16) + (1-alpha)*int(self.accent_color[5:7], 16)):02x}"
                self.rename_btn.config(bg=bg_color)
                self.root.update()
                self.root.after(10)
        self.rename_btn.bind("<Enter>", on_rename_enter)
        self.rename_btn.bind("<Leave>", on_rename_leave)
        
        # 文件位置按钮悬停效果
        def on_location_enter(e):
            # 平滑过渡到悬停颜色
            for i in range(10):
                alpha = i / 10
                bg_color = f"#{int((1-alpha)*int(self.light_bg[1:3], 16) + alpha*int(self.accent_color[1:3], 16)):02x}{int((1-alpha)*int(self.light_bg[3:5], 16) + alpha*int(self.accent_color[3:5], 16)):02x}{int((1-alpha)*int(self.light_bg[5:7], 16) + alpha*int(self.accent_color[5:7], 16)):02x}"
                self.location_btn.config(bg=bg_color)
                self.root.update()
                self.root.after(10)
        def on_location_leave(e):
            # 平滑过渡到原始颜色
            for i in range(10):
                alpha = i / 10
                bg_color = f"#{int(alpha*int(self.light_bg[1:3], 16) + (1-alpha)*int(self.accent_color[1:3], 16)):02x}{int(alpha*int(self.light_bg[3:5], 16) + (1-alpha)*int(self.accent_color[3:5], 16)):02x}{int(alpha*int(self.light_bg[5:7], 16) + (1-alpha)*int(self.accent_color[5:7], 16)):02x}"
                self.location_btn.config(bg=bg_color)
                self.root.update()
                self.root.after(10)
        self.location_btn.bind("<Enter>", on_location_enter)
        self.location_btn.bind("<Leave>", on_location_leave)
        
        # 视频画布 - 圆角边框效果
        self.canvas = tk.Canvas(self.video_frame, bg="#151515", 
                              highlightthickness=1, highlightbackground=self.border_color)
        self.canvas.pack(fill=tk.BOTH, expand=True)
        
        # 视频控制栏
        video_controls = tk.Frame(self.video_frame, bg=self.card_bg)
        video_controls.pack(fill=tk.X, pady=(16, 0))
        
        # 播放/暂停按钮
        button_frame = tk.Frame(video_controls, bg=self.card_bg)
        button_frame.pack(side=tk.LEFT, fill=tk.Y)
        
        self.play_btn = ttk.Button(button_frame, text="播放", command=self.play_video, 
                                  state=tk.DISABLED, style='Custom.TButton')
        self.play_btn.pack(side=tk.LEFT, padx=(0, 12))
        
        self.pause_video_btn = ttk.Button(button_frame, text="暂停", command=self.pause_video, 
                                        state=tk.DISABLED, style='Custom.TButton')
        self.pause_video_btn.pack(side=tk.LEFT)
        
        # 视频状态提示
        self.status_label = tk.Label(video_controls, text="状态: 未播放", 
                                    bg=self.card_bg, fg=self.secondary_text, 
                                    font=('Segoe UI', 9))
        self.status_label.pack(side=tk.RIGHT, padx=10)
        
        # 进度条区域 - 卡片式设计
        self.progress_frame = ttk.LabelFrame(self.left_frame, text="进度", padding=16, style='Custom.TLabelframe')
        self.progress_frame.pack(fill=tk.X)
        
        # 进度画布
        self.progress_canvas = tk.Canvas(self.progress_frame, height=120, bg=self.card_bg, 
                                      cursor="hand1", highlightthickness=1, 
                                      highlightbackground=self.border_color)
        self.progress_canvas.pack(fill=tk.X, pady=(12, 0))
        self.progress_canvas.bind('<Button-1>', self.on_progress_click)
        self.progress_canvas.bind('<B1-Motion>', self.on_progress_drag)
        self.progress_canvas.bind('<ButtonRelease-1>', self.on_progress_release)
        
        # 时间标签
        self.time_label = tk.Label(self.progress_frame, text="00:00 / 00:00", 
                                  font=('Arial', 9),
                                  bg=self.card_bg, fg=self.secondary_text)
        self.time_label.pack(side=tk.RIGHT, pady=(12, 0))
        
        # 常驻提示区域
        self.hints_frame = tk.Frame(self.progress_frame, bg=self.card_bg)
        self.hints_frame.pack(fill=tk.X, pady=(12, 0))
        
        # 进度旋钮提示
        self.knob_hint_frame = tk.Frame(self.hints_frame, bg=self.card_bg)
        self.knob_hint_frame.pack(side=tk.LEFT, padx=10, fill=tk.X, expand=True)
        self.knob_hint_label = tk.Label(self.knob_hint_frame, text="进度: 00:00:00", 
                                       bg=self.card_bg, fg=self.text_color, font=('Segoe UI', 9))
        self.knob_hint_label.pack(side=tk.LEFT, padx=5)
        self.knob_hint_entry = ttk.Entry(self.knob_hint_frame, width=15, style='Custom.TEntry')
        self.knob_hint_entry.pack(side=tk.LEFT, padx=5)
        self.knob_hint_entry.bind('<Return>', self.on_knob_hint_change)
        self.knob_hint_entry.bind('<FocusIn>', lambda e: self.knob_hint_frame.configure(cursor='ibeam'))
        self.knob_hint_entry.bind('<FocusOut>', lambda e: self.knob_hint_frame.configure(cursor=''))
        
        # 入点提示
        self.in_point_hint_frame = tk.Frame(self.hints_frame, bg=self.card_bg)
        self.in_point_hint_frame.pack(side=tk.LEFT, padx=10, fill=tk.X, expand=True)
        self.in_point_hint_label = tk.Label(self.in_point_hint_frame, text="截取入点: 00:00:00", 
                                          bg=self.card_bg, fg=self.text_color, font=('Segoe UI', 9))
        self.in_point_hint_label.pack(side=tk.LEFT, padx=5)
        self.in_point_hint_entry = ttk.Entry(self.in_point_hint_frame, width=15, style='Custom.TEntry')
        self.in_point_hint_entry.pack(side=tk.LEFT, padx=5)
        self.in_point_hint_entry.bind('<Return>', self.on_in_point_hint_change)
        self.in_point_hint_entry.bind('<FocusIn>', lambda e: self.in_point_hint_frame.configure(cursor='ibeam'))
        self.in_point_hint_entry.bind('<FocusOut>', lambda e: self.in_point_hint_frame.configure(cursor=''))
        
        # 出点提示
        self.out_point_hint_frame = tk.Frame(self.hints_frame, bg=self.card_bg)
        self.out_point_hint_frame.pack(side=tk.LEFT, padx=10, fill=tk.X, expand=True)
        self.out_point_hint_label = tk.Label(self.out_point_hint_frame, text="截取出点: 00:00:00", 
                                           bg=self.card_bg, fg=self.text_color, font=('Segoe UI', 9))
        self.out_point_hint_label.pack(side=tk.LEFT, padx=5)
        self.out_point_hint_entry = ttk.Entry(self.out_point_hint_frame, width=15, style='Custom.TEntry')
        self.out_point_hint_entry.pack(side=tk.LEFT, padx=5)
        self.out_point_hint_entry.bind('<Return>', self.on_out_point_hint_change)
        self.out_point_hint_entry.bind('<FocusIn>', lambda e: self.out_point_hint_frame.configure(cursor='ibeam'))
        self.out_point_hint_entry.bind('<FocusOut>', lambda e: self.out_point_hint_frame.configure(cursor=''))
        
        # 片段列表
        clip_list_frame = tk.Frame(self.right_frame)
        clip_list_frame.pack(fill=tk.BOTH, expand=True, pady=(12, 0))
        
        self.clip_listbox = tk.Listbox(clip_list_frame,
                                     width=35,
                                     bg=self.card_bg,
                                     fg=self.text_color,
                                     highlightthickness=1,
                                     highlightbackground=self.accent_color,
                                     selectbackground=self.light_bg,
                                     selectforeground=self.text_color,
                                     font=('Arial', 9),
                                     bd=1,
                                     relief='solid',
                                     activestyle='none')
        self.clip_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        # 片段列表滚动条
        clip_scrollbar = ttk.Scrollbar(clip_list_frame, orient=tk.VERTICAL, command=self.clip_listbox.yview)
        clip_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.clip_listbox.configure(yscrollcommand=clip_scrollbar.set)
        
        # 片段控制按钮
        clip_buttons = tk.Frame(self.right_frame, bg=self.card_bg)
        clip_buttons.pack(fill=tk.X, pady=(16, 0))
        
        ttk.Button(clip_buttons, text="播放选中", command=self.play_selected_clip, 
                  style='Custom.TButton').pack(side=tk.LEFT, padx=(0, 12))
        ttk.Button(clip_buttons, text="重命名", command=self.rename_selected_clip, 
                  style='Custom.TButton').pack(side=tk.LEFT, padx=(0, 12))
        ttk.Button(clip_buttons, text="文件位置", command=self.open_clip_location, 
                  style='Custom.TButton').pack(side=tk.LEFT, padx=(0, 12))
        ttk.Button(clip_buttons, text="删除片段", command=self.delete_selected_clip, 
                  style='Danger.TButton').pack(side=tk.LEFT)
        # 通知窗口
        self.notification = tk.Toplevel(self.root)
        self.notification.title("通知")
        self.notification.geometry("300x110")
        self.notification.transient(self.root)
        self.notification.withdraw()
        self.notification.configure(bg=self.card_bg)
        
        self.notification_label = tk.Label(self.notification, text="", 
                                         font=('Arial', 10),
                                         bg=self.card_bg, fg=self.text_color)
        self.notification_label.pack(pady=18)
        
        notification_buttons = tk.Frame(self.notification, bg=self.card_bg)
        notification_buttons.pack(pady=12)
        
        ttk.Button(notification_buttons, text="编辑", command=self.open_marker_edit, 
                  style='Custom.TButton').pack(side=tk.LEFT, padx=10)
        ttk.Button(notification_buttons, text="确定", command=self.notification.withdraw, 
                  style='Accent.TButton').pack(side=tk.LEFT, padx=10)
        
        # 标记编辑窗口
        self.marker_edit_window = tk.Toplevel(self.root)
        self.marker_edit_window.title("编辑标记")
        self.marker_edit_window.geometry("400x220")
        self.marker_edit_window.transient(self.root)
        self.marker_edit_window.withdraw()
        self.marker_edit_window.configure(bg=self.card_bg)
        
        tk.Label(self.marker_edit_window, text="标记名称:", 
                font=('Arial', 10),
                bg=self.card_bg, fg=self.text_color).pack(pady=10)
        self.marker_name_var = tk.StringVar()
        ttk.Entry(self.marker_edit_window, textvariable=self.marker_name_var, 
                 style='Custom.TEntry').pack(fill=tk.X, padx=20, pady=6)
        
        tk.Label(self.marker_edit_window, text="备注:", 
                font=('Arial', 10),
                bg=self.card_bg, fg=self.text_color).pack(pady=10)
        self.marker_note_var = tk.StringVar()
        ttk.Entry(self.marker_edit_window, textvariable=self.marker_note_var, 
                 style='Custom.TEntry').pack(fill=tk.X, padx=20, pady=6)
        
        button_frame = tk.Frame(self.marker_edit_window, bg=self.card_bg)
        button_frame.pack(pady=15)
        
        ttk.Button(button_frame, text="保存", command=self.save_marker_edit, 
                  style='Accent.TButton').pack(side=tk.LEFT, padx=12)
        ttk.Button(button_frame, text="取消", command=self.marker_edit_window.withdraw, 
                  style='Custom.TButton').pack(side=tk.LEFT, padx=12)
        
        self.current_marker_index = -1
        
        # 添加空格键快捷键绑定 - 标记进度
        def on_space_key(event):
            # 如果正在录屏且处于暂停状态，不执行标记
            if self.recording and self.paused:
                return 'break'
            self.mark_progress()
            return 'break'  # 阻止空格键的默认行为
        self.root.bind('<space>', on_space_key)

    def start_recording(self):
        screen_width, screen_height = pyautogui.size()
        self.x = 0
        self.y = 0
        self.width = screen_width
        self.height = screen_height
        
        self.recording = True
        self.paused = False
        
        # 最小化主窗口
        self.root.iconify()
        
        # 录制时：显示暂停、结束、标记按钮，隐藏开始按钮
        self.start_btn.grid_remove()
        self.pause_btn.grid(row=0, column=0, padx=6, pady=2)
        self.stop_btn.grid(row=0, column=1, padx=6, pady=2)
        self.mark_btn.grid(row=0, column=2, padx=6, pady=2)
        self.clip_btn.config(state=tk.DISABLED)
        
        # 取消截取视频状态
        self.clip_mode = False
        self.clip_btn.config(text="截取视频", state=tk.NORMAL)
        self.finish_clip_btn.config(state=tk.DISABLED)
        
        # 设置视频文件路径
        timestamp = time.strftime('%Y%m%d_%H%M%S')
        
        # 创建会话目录 - 使用用户文档目录确保权限
        self.current_session_dir = os.path.join(self.recordings_dir, timestamp)
        if not os.path.exists(self.current_session_dir):
            os.makedirs(self.current_session_dir)
            print(f"[录制] 创建会话目录: {self.current_session_dir}")
        
        # 创建截取视频文件夹
        clip_folder = os.path.join(self.current_session_dir, self.clip_dir)
        if not os.path.exists(clip_folder):
            os.makedirs(clip_folder)
        
        # 设置视频文件路径
        self.video_file = os.path.join(self.current_session_dir, f"recording_{timestamp}.avi")
        
        # 重置标记和片段相关变量
        self.markers = []
        self.marker_count = 0
        self.clips = []
        
        # 立即创建 markers.json（即使没有标记，用于工具校验）
        self.save_markers_to_file()
        
        # 重置视频文件名标签和修改按钮
        self.video_filename_label.config(text="")
        self.rename_btn.pack_forget()  # 隐藏修改按钮
        
        self.recording_start_time = time.time()
        self.current_time = 0
        self.recorded_frames = 0
        self.update_thread = threading.Thread(target=self.update_progress)
        self.stop_update = False
        self.update_thread.daemon = True
        self.update_thread.start()
        self.recorder = cv2.VideoWriter(self.video_file, cv2.VideoWriter_fourcc(*'XVID'), 10.0, (self.width, self.height))
        self.record_thread = threading.Thread(target=self.record_screen)
        self.record_thread.daemon = True
        self.record_thread.start()
        
        # 创建缩略功能区
        self.create_mini_control()
        
        # 最小化主窗口
        self.root.iconify()
        
        self.show_notification("开始录屏", is_weak=True)
    
    def pause_recording(self):
        if self.paused:
            # 从暂停状态恢复
            self.paused = False
            self.pause_btn.config(text="暂停录屏")
            # 更新缩略功能区的按钮文本
            if hasattr(self, 'mini_pause_btn') and self.mini_pause_btn:
                self.mini_pause_btn.config(text="暂停录屏")
            # 更新状态标签
            if hasattr(self, 'mini_status_label') and self.mini_status_label:
                self.mini_status_label.config(text="录屏中...", foreground='green')
            # 启用标记进度按钮
            self.mark_btn.config(state=tk.NORMAL)
            if hasattr(self, 'mini_mark_btn') and self.mini_mark_btn:
                self.mini_mark_btn.config(state=tk.NORMAL)
            # 调整 recording_start_time，跳过暂停的时间
            if hasattr(self, 'pause_start_time'):
                pause_duration = time.time() - self.pause_start_time
                self.recording_start_time += pause_duration
                delattr(self, 'pause_start_time')
            self.show_notification("继续录屏", is_weak=True)
        else:
            # 进入暂停状态
            self.paused = True
            # 记录暂停开始时间
            self.pause_start_time = time.time()
            self.pause_btn.config(text="继续录屏")
            # 更新缩略功能区的按钮文本
            if hasattr(self, 'mini_pause_btn') and self.mini_pause_btn:
                self.mini_pause_btn.config(text="继续录屏")
            # 更新状态标签
            if hasattr(self, 'mini_status_label') and self.mini_status_label:
                self.mini_status_label.config(text="已暂停", foreground='orange')
            # 禁用标记进度按钮
            self.mark_btn.config(state=tk.DISABLED)
            if hasattr(self, 'mini_mark_btn') and self.mini_mark_btn:
                self.mini_mark_btn.config(state=tk.DISABLED)
            self.show_notification("暂停录屏", is_weak=True)
    
    def stop_recording(self):
        self.recording = False
        # 如果处于暂停状态，先调整 recording_start_time
        if self.paused and hasattr(self, 'pause_start_time'):
            self.recording_start_time += time.time() - self.pause_start_time
            delattr(self, 'pause_start_time')
        # 未录制时：显示开始按钮，隐藏暂停、结束、标记按钮
        self.pause_btn.grid_remove()
        self.stop_btn.grid_remove()
        self.mark_btn.grid_remove()
        self.start_btn.grid(row=0, column=0, padx=6, pady=2)
        self.clip_btn.config(state=tk.NORMAL)
        self.stop_update = True
        if self.update_thread:
            self.update_thread.join(timeout=1)
        if self.recorder:
            self.recorder.release()
        
        # 等待录屏线程结束
        if hasattr(self, 'record_thread') and self.record_thread:
            self.record_thread.join(timeout=2)
        
        # 关闭缩略功能区
        self.close_mini_control()
        
        # 恢复主窗口
        self.root.deiconify()
        
        if self.video_file and os.path.exists(self.video_file):
            # 计算视频实际时长
            self.calculate_video_duration()
            
            # 保存当前视频的标记和片段
            self.video_markers[self.video_file] = self.markers.copy()
            self.video_clips[self.video_file] = self.clips.copy()
            
            # 保存 markers.json（即使没有标记也要保存，用于工具校验）
            self.save_markers_to_file()
            
            self.play_btn.config(state=tk.NORMAL)
            self.show_notification("录屏完成", is_weak=True)
            self.save_recording_path()
            # 显示视频第一帧
            self.show_first_frame()
    
    def open_video_location(self):
        """打开视频文件所在的目录并选中该文件"""
        if not self.video_file or not os.path.exists(self.video_file):
            return
        
        try:
            # 打开目录并选中文件
            if os.name == 'nt':  # Windows
                # 使用 explorer.exe /select 命令选中文件
                import subprocess
                subprocess.run(['explorer.exe', '/select,', self.video_file])
            elif os.name == 'posix':  # macOS/Linux
                if 'darwin' in sys.platform:  # macOS
                    import subprocess
                    subprocess.run(['open', '-R', self.video_file])
                else:  # Linux
                    # 尝试使用常见的文件管理器
                    import subprocess
                    try:
                        # 尝试 Nautilus (GNOME)
                        subprocess.run(['nautilus', '--select', self.video_file])
                    except FileNotFoundError:
                        try:
                            # 尝试 Dolphin (KDE)
                            subprocess.run(['dolphin', '--select', self.video_file])
                        except FileNotFoundError:
                            # 尝试 Thunar (Xfce)
                            subprocess.run(['thunar', '--select', self.video_file])
        except Exception as e:
            print(f"打开文件位置失败: {e}")
            self.show_notification("打开文件位置失败", is_weak=True)
    
    def open_clip_location(self):
        """打开选中片段所在的目录并选中该文件"""
        if not self.current_session_dir:
            return
        
        try:
            # 获取截取视频文件夹
            clip_dir = os.path.join(self.current_session_dir, self.clip_dir)
            # 确保目录存在
            if not os.path.exists(clip_dir):
                os.makedirs(clip_dir)
            
            # 获取选中的片段
            selected_index = self.clip_listbox.curselection()
            if selected_index:
                # 构建选中片段的文件路径
                clip_index = selected_index[0]
                if clip_index < len(self.clips):
                    clip = self.clips[clip_index]
                    # 检查片段是否有文件夹名称（新结构）
                    if 'folder_name' in clip:
                        # 新结构：片段在单独的文件夹中
                        clip_folder = os.path.join(clip_dir, clip['folder_name'])
                        clip_file = os.path.join(clip_folder, "clip.avi")
                    else:
                        # 旧结构：直接在截取视频文件夹中
                        clip_id = clip.get('id', clip_index + 1)
                        if 'name' in clip and clip['name']:
                            clip_file = os.path.join(clip_dir, f"{clip['name']}.avi")
                        else:
                            # 获取当前视频的文件名（不含路径和后缀）
                            video_filename = ""
                            if self.video_file:
                                basename = os.path.basename(self.video_file)
                                video_filename = os.path.splitext(basename)[0] + "_"
                            # 使用与显示名称一致的格式
                            clip_file = os.path.join(clip_dir, f"{video_filename}片段 {clip_id}.avi")
                    
                    # 打开目录并选中文件
                    if os.path.exists(clip_file):
                        if os.name == 'nt':  # Windows
                            import subprocess
                            subprocess.run(['explorer.exe', '/select,', clip_file])
                        elif os.name == 'posix':  # macOS/Linux
                            if 'darwin' in sys.platform:  # macOS
                                import subprocess
                                subprocess.run(['open', '-R', clip_file])
                            else:  # Linux
                                # 尝试使用常见的文件管理器
                                import subprocess
                                try:
                                    # 尝试 Nautilus (GNOME)
                                    subprocess.run(['nautilus', '--select', clip_file])
                                except FileNotFoundError:
                                    try:
                                        # 尝试 Dolphin (KDE)
                                        subprocess.run(['dolphin', '--select', clip_file])
                                    except FileNotFoundError:
                                        # 尝试 Thunar (Xfce)
                                        subprocess.run(['thunar', '--select', clip_file])
                        return
            
            # 如果没有选中片段或片段文件不存在，只打开目录
            if os.name == 'nt':  # Windows
                os.startfile(clip_dir)
            else:  # macOS/Linux
                import subprocess
                subprocess.call(['open', clip_dir])
        except Exception as e:
            print(f"打开文件位置失败: {e}")
            self.show_notification("打开文件位置失败", is_weak=True)
    
    def rename_selected_clip(self):
        """重命名选中的片段"""
        selected_index = self.clip_listbox.curselection()
        if not selected_index:
            self.show_notification("请先选择要重命名的片段", is_weak=True)
            return
        
        clip_index = selected_index[0]
        if clip_index >= len(self.clips):
            return
        
        clip = self.clips[clip_index]
        clip_id = clip.get('id', clip_index + 1)
        
        # 创建重命名窗口
        rename_window = tk.Toplevel(self.root)
        rename_window.title("重命名片段")
        rename_window.geometry("400x150")
        rename_window.configure(bg=self.card_bg)
        rename_window.resizable(False, False)
        rename_window.attributes('-topmost', True)
        
        # 居中显示
        rename_window.update_idletasks()
        screen_width = rename_window.winfo_screenwidth()
        screen_height = rename_window.winfo_screenheight()
        x = (screen_width - 400) // 2
        y = (screen_height - 150) // 2
        rename_window.geometry(f"400x150+{x}+{y}")
        
        # 当前名称
        if 'name' in clip and clip['name']:
            current_name = clip['name']
        else:
            # 获取当前视频的文件名（不含路径和后缀）
            video_filename = ""
            if self.video_file:
                basename = os.path.basename(self.video_file)
                video_filename = os.path.splitext(basename)[0] + "_"
            # 使用与系统文件名一致的格式
            current_name = f"{video_filename}片段 {clip_id}"
        
        # 标签
        tk.Label(rename_window, text="输入新的片段名称：", 
                font=('Arial', 10), bg=self.card_bg, fg=self.text_color).pack(pady=(15, 5))
        
        # 输入框框架
        input_frame = tk.Frame(rename_window, bg=self.card_bg)
        input_frame.pack(pady=5)
        
        # 名称输入框
        name_var = tk.StringVar(value=current_name)
        name_entry = tk.Entry(input_frame, textvariable=name_var, 
                             font=('Arial', 10), width=30)
        name_entry.pack(side=tk.LEFT, padx=(0, 5))
        name_entry.select_range(0, tk.END)
        name_entry.focus()
        
        # 后缀标签
        tk.Label(input_frame, text=".avi", 
                font=('Arial', 10), bg=self.card_bg, fg=self.text_color).pack(side=tk.LEFT)
        
        # 按钮框架
        button_frame = tk.Frame(rename_window, bg=self.card_bg)
        button_frame.pack(pady=15)
        
        # 确定按钮
        def confirm_rename():
            new_name = name_var.get().strip()
            if not new_name:
                messagebox.showerror("错误", "名称不能为空")
                return
            
            # 检查新名称是否已存在
            clip_dir = os.path.join(self.current_session_dir, self.clip_dir)
            
            # 检查是否与其他文件重名（包括文件夹）
            duplicate_found = False
            if os.path.exists(clip_dir):
                for item in os.listdir(clip_dir):
                    if item == new_name:
                        duplicate_found = True
                        break
            
            if duplicate_found:
                self.show_notification("已存在重名文件或文件夹", is_weak=True, parent=rename_window)
                return
            
            try:
                # 获取片段在self.clips中的实际索引
                actual_clip_index = None
                for idx, c in enumerate(self.clips):
                    if c.get('id') == clip_id:
                        actual_clip_index = idx
                        break
                
                print(f"[DEBUG] 重命名片段: clip_id={clip_id}, actual_index={actual_clip_index}")
                print(f"[DEBUG] 当前片段信息: {self.clips[actual_clip_index] if actual_clip_index is not None else 'Not found'}")
                
                # 检查是否有folder_name（新结构）或者尝试构建folder_name
                current_clip = self.clips[actual_clip_index]
                has_folder_name = 'folder_name' in current_clip and current_clip['folder_name']
                
                if has_folder_name:
                    # 新结构：重命名文件夹
                    old_folder = os.path.join(clip_dir, current_clip['folder_name'])
                    new_folder = os.path.join(clip_dir, new_name)
                    
                    if os.path.exists(old_folder):
                        os.rename(old_folder, new_folder)
                        print(f"片段文件夹已重命名: {old_folder} -> {new_folder}")
                    else:
                        print(f"警告：原文件夹不存在: {old_folder}")
                    
                    # 更新片段信息（更新到self.clips）
                    self.clips[actual_clip_index]['folder_name'] = new_name
                    self.clips[actual_clip_index]['name'] = new_name
                    print(f"[DEBUG] 更新self.clips[{actual_clip_index}]完成")
                    
                    # 更新签名文件
                    self.create_clip_signature(new_folder, self.clips[actual_clip_index])
                else:
                    # 旧结构或混合结构：需要处理文件夹
                    video_filename = ""
                    if self.video_file:
                        basename = os.path.basename(self.video_file)
                        video_filename = os.path.splitext(basename)[0] + "_"
                    
                    # 尝试构建文件夹名（与finish_clip中一致的格式）
                    old_folder_name = f"{video_filename}片段_{clip_id}"
                    old_folder = os.path.join(clip_dir, old_folder_name)
                    new_folder = os.path.join(clip_dir, new_name)
                    
                    print(f"[DEBUG] 尝试旧结构重命名: {old_folder} -> {new_folder}")
                    
                    if os.path.exists(old_folder):
                        os.rename(old_folder, new_folder)
                        print(f"片段文件夹已重命名（旧结构）: {old_folder} -> {new_folder}")
                        # 更新片段信息
                        self.clips[actual_clip_index]['folder_name'] = new_name
                        self.clips[actual_clip_index]['name'] = new_name
                        # 更新签名文件
                        self.create_clip_signature(new_folder, self.clips[actual_clip_index])
                    else:
                        # 旧结构文件方式（无文件夹）
                        new_file = os.path.join(clip_dir, f"{new_name}.avi")
                        old_file = os.path.join(clip_dir, f"{video_filename}片段 {clip_id}.avi")
                        
                        if os.path.exists(old_file):
                            os.rename(old_file, new_file)
                            print(f"片段文件已重命名（旧结构）: {old_file} -> {new_file}")
                        
                        # 更新片段信息
                        self.clips[actual_clip_index]['name'] = new_name
                
                # 更新视频片段字典
                if self.video_file in self.video_clips:
                    for c in self.video_clips[self.video_file]:
                        if c['id'] == clip_id:
                            c['name'] = new_name
                            if 'folder_name' in self.clips[actual_clip_index]:
                                c['folder_name'] = new_name
                            print(f"[DEBUG] 更新video_clips完成: {c}")
                            break
                
                # 更新片段列表
                self.update_clips()
                
                # 关闭窗口
                rename_window.destroy()
                
                self.show_notification("片段重命名成功", is_weak=True)
            except Exception as e:
                print(f"重命名失败: {e}")
                import traceback
                traceback.print_exc()
                messagebox.showerror("错误", f"重命名失败：{str(e)}")
        
        # 取消按钮
        def cancel_rename():
            rename_window.destroy()
        
        ttk.Button(button_frame, text="确定", command=confirm_rename, style='Accent.TButton').pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="取消", command=cancel_rename, style='Custom.TButton').pack(side=tk.LEFT, padx=5)
    
    def rename_video_file(self):
        """修改视频文件名"""
        if not self.video_file or not os.path.exists(self.video_file):
            return
        
        # 创建弹窗
        rename_window = tk.Toplevel(self.root)
        rename_window.title("修改文件名")
        rename_window.geometry("400x150")
        rename_window.configure(bg=self.card_bg)
        rename_window.resizable(False, False)
        rename_window.attributes('-topmost', True)
        
        # 居中显示
        rename_window.update_idletasks()
        screen_width = rename_window.winfo_screenwidth()
        screen_height = rename_window.winfo_screenheight()
        x = (screen_width - 400) // 2
        y = (screen_height - 150) // 2
        rename_window.geometry(f"400x150+{x}+{y}")
        
        # 当前文件名
        current_filename = os.path.basename(self.video_file)
        # 提取不带后缀的文件名
        name_without_ext = os.path.splitext(current_filename)[0]
        
        # 标签
        tk.Label(rename_window, text="输入新的文件名：", 
                font=('Arial', 10), bg=self.card_bg, fg=self.text_color).pack(pady=(15, 5))
        
        # 输入框框架
        input_frame = tk.Frame(rename_window, bg=self.card_bg)
        input_frame.pack(pady=5)
        
        # 文件名输入框
        filename_var = tk.StringVar(value=name_without_ext)
        filename_entry = tk.Entry(input_frame, textvariable=filename_var, 
                                 font=('Arial', 10), width=30)
        filename_entry.pack(side=tk.LEFT, padx=(0, 5))
        filename_entry.select_range(0, tk.END)
        filename_entry.focus()
        
        # 后缀标签
        tk.Label(input_frame, text=".avi", 
                font=('Arial', 10), bg=self.card_bg, fg=self.text_color).pack(side=tk.LEFT)
        
        # 按钮框架
        button_frame = tk.Frame(rename_window, bg=self.card_bg)
        button_frame.pack(pady=15)
        
        # 确定按钮
        def confirm_rename():
            new_name = filename_var.get().strip()
            if not new_name:
                messagebox.showerror("错误", "文件名不能为空")
                return
            
            # 新的文件路径
            new_filename = new_name + ".avi"
            
            # 检查新文件名是否已存在于recordings目录及子文件夹中
            duplicate_found = False
            for root, dirs, files in os.walk(self.recordings_dir):
                if new_filename in files:
                    duplicate_found = True
                    break
            
            if duplicate_found:
                self.show_notification("已存在重名文件", is_weak=True, parent=rename_window)
                return
            
            new_video_file = os.path.join(os.path.dirname(self.video_file), new_filename)
            
            try:
                # 重命名文件
                os.rename(self.video_file, new_video_file)
                
                # 更新当前视频文件路径
                old_video_file = self.video_file
                self.video_file = new_video_file
                
                # 更新video_markers和video_clips中的键
                if old_video_file in self.video_markers:
                    self.video_markers[new_video_file] = self.video_markers.pop(old_video_file)
                if old_video_file in self.video_clips:
                    self.video_clips[new_video_file] = self.video_clips.pop(old_video_file)
                
                # 更新文件名标签
                self.video_filename_label.config(text=new_filename)
                
                # 更新片段列表显示（同步修改后的文件名）
                self.update_clips()
                
                # 关闭弹窗
                rename_window.destroy()
                
                self.show_notification("文件名修改成功", is_weak=True)
            except Exception as e:
                messagebox.showerror("错误", f"重命名失败：{str(e)}")
        
        # 取消按钮
        def cancel_rename():
            rename_window.destroy()
        
        ttk.Button(button_frame, text="确定", command=confirm_rename, style='Accent.TButton').pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="取消", command=cancel_rename, style='Custom.TButton').pack(side=tk.LEFT, padx=5)
    
    def show_first_frame(self):
        """显示视频的第一帧画面"""
        if not self.video_file or not os.path.exists(self.video_file):
            return

        # 计算视频时长
        self.calculate_video_duration()
        
        # 加载当前视频的标记 - 优先从文件加载
        saved_markers = self.load_markers_from_file()
        if saved_markers:
            self.markers = saved_markers
            self.video_markers[self.video_file] = saved_markers.copy()
            self.marker_count = len(self.markers)
        elif self.video_file in self.video_markers:
            self.markers = self.video_markers[self.video_file].copy()
            self.marker_count = len(self.markers)
        else:
            self.markers = []
            self.marker_count = 0
        
        # 加载当前视频的片段
        print(f"\n=== 加载片段 ===")
        print(f"当前视频文件: {self.video_file}")
        print(f"当前会话目录: {self.current_session_dir}")
        print(f"video_clips中是否存在: {self.video_file in self.video_clips}")
        
        if self.video_file in self.video_clips:
            # 从内存中加载片段
            print(f"从内存加载片段，数量: {len(self.video_clips[self.video_file])}")
            self.clips = self.video_clips[self.video_file].copy()
        else:
            # 从文件系统读取片段
            self.clips = []
            # 检查截取视频文件夹
            if self.current_session_dir:
                clip_dir = os.path.join(self.current_session_dir, self.clip_dir)
                print(f"截取视频文件夹路径: {clip_dir}")
                print(f"截取视频文件夹存在: {os.path.exists(clip_dir)}")
                
                if os.path.exists(clip_dir):
                    items = os.listdir(clip_dir)
                    print(f"截取视频文件夹中的项目数量: {len(items)}")
                    
                    # 查找子目录（每个片段一个文件夹）
                    for item in items:
                        item_path = os.path.join(clip_dir, item)
                        if os.path.isdir(item_path):
                            # 验证这个文件夹是否是有效的片段文件夹
                            is_valid, error_msg, clip_info = self.is_valid_clip_folder(item_path)
                            print(f"检查文件夹: {item}, 有效: {is_valid}, 错误: {error_msg}")
                            
                            if is_valid:
                                print(f"找到有效片段文件夹: {item}")
                                # 从签名文件中获取片段信息，或者构建默认信息
                                clip = clip_info if clip_info else {
                                    "id": len(self.clips) + 1,
                                    "start": 0,
                                    "end": 0,
                                    "duration": 0
                                }
                                # 记录文件夹名称，用于后续操作
                                clip["folder_name"] = item
                                self.clips.append(clip)
                                print(f"添加片段: ID={clip.get('id', len(self.clips))}")
                            else:
                                print(f"跳过无效片段文件夹 {item}: {error_msg}")
            print(f"总共添加 {len(self.clips)} 个片段")
            # 保存到video_clips字典
            self.video_clips[self.video_file] = self.clips.copy()
        
        # 更新片段列表
        self.update_clips()
        
        # 更新视频文件名标签和修改按钮
        if self.video_file:
            # 提取文件名
            filename = os.path.basename(self.video_file)
            self.video_filename_label.config(text=filename)
            self.rename_btn.pack(side=tk.LEFT, padx=(10, 0))  # 显示修改按钮
            self.location_btn.pack(side=tk.LEFT, padx=(10, 0))  # 显示文件位置按钮
        else:
            self.video_filename_label.config(text="")
            self.rename_btn.pack_forget()  # 隐藏修改按钮
            self.location_btn.pack_forget()  # 隐藏文件位置按钮
        
        cap = cv2.VideoCapture(self.video_file)
        if not cap.isOpened():
            cap.release()
            return
        
        # 读取第一帧
        ret, frame = cap.read()
        cap.release()
        
        if not ret:
            return
        
        # 转换颜色空间
        frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
        
        # 获取画布尺寸并缩放
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()
        
        if canvas_width > 0 and canvas_height > 0:
            img = Image.fromarray(frame)
            img_width, img_height = img.size
            canvas_ratio = canvas_width / canvas_height
            img_ratio = img_width / img_height
            
            if canvas_ratio > img_ratio:
                new_height = canvas_height
                new_width = int(img_width * (canvas_height / img_height))
            else:
                new_width = canvas_width
                new_height = int(img_height * (canvas_width / img_width))
            
            img = img.resize((new_width, new_height), Image.LANCZOS)
            imgtk = ImageTk.PhotoImage(image=img)
            
            # 居中显示
            x_offset = (canvas_width - new_width) // 2
            y_offset = (canvas_height - new_height) // 2
            self.canvas.create_image(x_offset, y_offset, anchor=tk.NW, image=imgtk)
            self.canvas.imgtk = imgtk
        
        # 更新进度条，显示当前视频的标记
        self.update_progress_bar()

        # 启用播放按钮和截取视频按钮
        self.play_btn.config(state=tk.NORMAL)
        self.clip_btn.config(state=tk.NORMAL)
    
    def record_screen(self):
        frame_interval = 1.0 / 10.0  # 10 FPS = 每帧100ms
        next_frame_time = time.time()
        frame_count = 0
        start_time = time.time()
        
        while self.recording:
            if not self.paused:
                frame_start = time.time()
                
                screenshot = pyautogui.screenshot(region=(self.x, self.y, self.width, self.height))
                frame = np.array(screenshot)
                frame = cv2.cvtColor(frame, cv2.COLOR_RGB2BGR)
                self.recorder.write(frame)
                self.recorded_frames += 1
                frame_count += 1
                
                frame_write_time = time.time() - frame_start
                
                # 移动到下一帧的目标时间
                next_frame_time += frame_interval
                
                # 等待到目标时间（如果还没到）
                current_time = time.time()
                sleep_time = next_frame_time - current_time
                
                if frame_count <= 100 or frame_count % 100 == 0:  # 前100帧和每100帧打印一次
                    elapsed_total = current_time - start_time
                    actual_fps = frame_count / elapsed_total if elapsed_total > 0 else 0
                    print(f"[录帧] #{frame_count:4d} | 写帧:{frame_write_time*1000:.1f}ms | 等待:{max(0, sleep_time)*1000:.1f}ms | 实际FPS:{actual_fps:.2f} | total:{elapsed_total:.1f}s")
                
                if sleep_time > 0:
                    time.sleep(sleep_time)
            else:
                # 暂停时重置下一帧时间基准
                next_frame_time = time.time()
                time.sleep(0.1)
    
    def save_markers_to_file(self):
        """保存标记信息到会话目录的JSON文件（包含工具校验码）"""
        if not self.current_session_dir:
            print("[保存] 跳过：当前会话目录为空")
            return
        
        markers_file = os.path.join(self.current_session_dir, "markers.json")
        try:
            # 先测试目录是否可写
            test_file = os.path.join(self.current_session_dir, ".test_write")
            with open(test_file, 'w') as f:
                f.write("test")
            os.remove(test_file)
            print(f"[保存] 目录可写: {self.current_session_dir}")
            
            data = {
                "tool_signature": "live_recorder_marker_tool_v1",
                "markers": self.markers
            }
            with open(markers_file, 'w', encoding='utf-8') as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
            print(f"[保存] 标记已保存到: {markers_file}")
            print(f"[保存] 标记数量: {len(self.markers)}")
            
            # 验证文件是否真的存在
            if os.path.exists(markers_file):
                file_size = os.path.getsize(markers_file)
                print(f"[保存] 文件大小: {file_size} 字节")
            else:
                print(f"[警告] 文件创建后不存在！")
                
        except Exception as e:
            print(f"[错误] 保存标记失败: {type(e).__name__}: {e}")
            import traceback
            traceback.print_exc()
    
    def load_markers_from_file(self):
        """从会话目录的JSON文件加载标记信息（兼容新旧格式）"""
        if not self.current_session_dir:
            return []
        
        markers_file = os.path.join(self.current_session_dir, "markers.json")
        if os.path.exists(markers_file):
            try:
                with open(markers_file, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                # 兼容新旧格式
                if isinstance(data, dict) and "markers" in data:
                    markers = data["markers"]
                else:
                    markers = data  # 旧格式：直接是标记数组
                print(f"从 {markers_file} 加载了 {len(markers)} 个标记")
                return markers
            except Exception as e:
                print(f"加载标记失败: {e}")
        return []
    
    def is_valid_tool_session(self, session_path):
        """
        验证会话目录是否为此工具产生的
        
        返回: (is_valid, error_message)
        """
        session_dir = os.path.basename(session_path)
        
        # 条件 1：目录名格式正确（YYYYMMDD_HHMMSS）
        if len(session_dir) != 15 or session_dir[8] != '_':
            return False, "目录名格式不正确"
        date_part = session_dir[:8]
        time_part = session_dir[9:]
        if not date_part.isdigit() or not time_part.isdigit():
            return False, "目录名格式不正确"
        
        # 条件 2：查找主视频文件
        clip_dir = os.path.join(session_path, self.clip_dir)
        all_files = os.listdir(session_path) if os.path.exists(session_path) else []
        video_files = [f for f in all_files if f.endswith('.avi') and os.path.join(session_path, f) != clip_dir]
        if os.path.exists(clip_dir):
            clip_avi_files = [f for f in os.listdir(clip_dir) if f.endswith('.avi')]
            video_files = [f for f in video_files if f not in clip_avi_files]
        
        if not video_files:
            return False, "未找到主视频文件"
        
        video_file = video_files[0]
        
        # 条件 3：文件名格式正确
        if not video_file.startswith('recording_') or not video_file.endswith('.avi'):
            return False, "文件名格式不正确"
        
        # 条件 4：文件名与目录名匹配
        expected_filename = f"recording_{session_dir}.avi"
        if video_file != expected_filename:
            return False, "文件名与目录名不匹配"
        
        # 条件 5：存在 markers.json 文件
        markers_file = os.path.join(session_path, "markers.json")
        if not os.path.exists(markers_file):
            return False, "未找到标记文件"
        
        # 条件 6：校验工具签名
        try:
            with open(markers_file, 'r', encoding='utf-8') as f:
                data = json.load(f)
            if isinstance(data, dict) and data.get("tool_signature") != "live_recorder_marker_tool_v1":
                return False, "无效的工具签名"
        except Exception:
            return False, "标记文件格式错误"
        
        return True, ""
    
    def create_clip_signature(self, clip_folder_path, clip_info):
        """
        为截取的片段创建工具签名验证文件
        
        参数:
            clip_folder_path: 片段文件夹路径
            clip_info: 片段信息字典
        """
        try:
            # 构建签名数据
            signature_data = {
                "tool_signature": "live_recorder_marker_tool_v1",
                "clip_info": clip_info,
                "create_time": time.strftime('%Y%m%d_%H%M%S')
            }
            
            # 保存为 JSON 文件
            signature_file = os.path.join(clip_folder_path, "clip_info.json")
            with open(signature_file, 'w', encoding='utf-8') as f:
                json.dump(signature_data, f, ensure_ascii=False, indent=2)
            
            print(f"片段签名文件已创建: {signature_file}")
            return True
        except Exception as e:
            print(f"创建片段签名失败: {e}")
            return False
    
    def is_valid_clip_folder(self, clip_folder_path):
        """
        验证片段文件夹是否为此工具产生的
        
        参数:
            clip_folder_path: 片段文件夹路径
        
        返回: (is_valid, error_message, clip_info)
        """
        # 检查是否存在 clip_info.json 文件
        signature_file = os.path.join(clip_folder_path, "clip_info.json")
        if not os.path.exists(signature_file):
            return False, "未找到片段签名文件", None
        
        # 检查工具签名
        try:
            with open(signature_file, 'r', encoding='utf-8') as f:
                data = json.load(f)
            
            if isinstance(data, dict) and data.get("tool_signature") != "live_recorder_marker_tool_v1":
                return False, "无效的片段工具签名", None
            
            clip_info = data.get("clip_info", {})
            return True, "", clip_info
        except Exception as e:
            print(f"验证片段签名失败: {e}")
            return False, "片段签名文件格式错误", None
    
    def calculate_video_duration(self):
        if self.video_file:
            cap = cv2.VideoCapture(self.video_file)
            if cap.isOpened():
                fps = cap.get(cv2.CAP_PROP_FPS)
                frame_count = cap.get(cv2.CAP_PROP_FRAME_COUNT)
                if fps > 0:
                    self.video_duration = frame_count / fps
                cap.release()
    
    def update_progress_bar(self):
        self.progress_canvas.delete('all')
        width = self.progress_canvas.winfo_width()
        height = self.progress_canvas.winfo_height()
        if width == 0 or height == 0:
            return
        
        # 添加留白区域
        padding = 20  # 左右留白的宽度
        usable_width = width - 2 * padding
        
        if self.video_duration > 0:
            progress = self.current_time / self.video_duration
        else:
            progress = 0
        
        # 绘制背景
        self.progress_canvas.create_rectangle(0, 0, width, height, fill="#333", outline="")
        
        # 绘制进度条（在画布下方，考虑留白）
        progress_bar_y = height - 30
        progress_bar_height = 20
        progress_width = int(usable_width * progress)
        self.progress_canvas.create_rectangle(padding, progress_bar_y, width - padding, progress_bar_y + progress_bar_height, fill="#444", outline="")
        self.progress_canvas.create_rectangle(padding, progress_bar_y, padding + progress_width, progress_bar_y + progress_bar_height, fill="#4CAF50", outline="")
        
        # 绘制黄色标记（在进度条上方）- 水滴形
        if self.recording or self.video_duration > 0:
            # 在录制模式下，使用 current_time 作为总时长
            # 在播放模式下，使用 video_duration 或所有标记的最大时间
            max_marker_time = 0
            if self.recording:
                total_duration = self.current_time if self.current_time > 0 else 1
            else:
                # 如果 video_duration 为0或小于任何标记的时间，使用标记的最大时间
                max_marker_time = max([m["time"] for m in self.markers]) if self.markers else 0
                if self.video_duration <= 0 or self.video_duration < max_marker_time:
                    total_duration = max_marker_time if max_marker_time > 0 else 1
                else:
                    total_duration = self.video_duration
            print(f"[调试] 绘制标记: 录制模式={self.recording}, video_duration={self.video_duration:.2f}, max_marker_time={max_marker_time:.2f}, total_duration={total_duration:.2f}, 标记数量={len(self.markers)}")
            if total_duration > 0:
                for idx, marker in enumerate(self.markers):
                    marker_time = marker["time"]
                    print(f"[调试] 标记时间: {marker_time:.2f}, 条件: {marker_time} <= {total_duration}")
                    if marker_time <= total_duration:
                        marker_pos = padding + (marker_time / total_duration) * usable_width
                        # 确保标记不会超出画布边界
                        marker_pos = max(padding + 4, min(width - padding - 4, marker_pos))
                        print(f"[调试] 绘制标记: 位置={marker_pos:.2f}, 时间={marker_time:.2f}, 画布宽度={width}")
                        
                        # 获取标记名称
                        marker_name = marker.get("name", str(idx + 1))
                        
                        # 绘制葫芦形标记（上面大圆、下面小圆，中间连接）
                        marker_pos_x = marker_pos
                        marker_top = progress_bar_y - 20
                        
                        # 葫芦形的多边形点（近似SVG葫芦形状）
                        # 上面大圆部分
                        gourd_points = [
                            marker_pos_x - 20, marker_top - 25,  # 左上
                            marker_pos_x - 10, marker_top - 30,  # 上尖
                            marker_pos_x + 10, marker_top - 30,  # 右上
                            marker_pos_x + 20, marker_top - 25,  # 右中
                            marker_pos_x + 20, marker_top - 10,  # 右下
                            marker_pos_x + 14, marker_top - 5,   # 腰部右
                            marker_pos_x + 14, marker_top + 5,   # 颈部右
                            marker_pos_x + 6, marker_top + 10,   # 底部右
                            marker_pos_x, marker_top + 20,       # 底部尖
                            marker_pos_x - 6, marker_top + 10,   # 底部左
                            marker_pos_x - 14, marker_top + 5,   # 颈部左
                            marker_pos_x - 14, marker_top - 5,   # 腰部左
                            marker_pos_x - 20, marker_top - 10,  # 左下
                            marker_pos_x - 20, marker_top - 25,  # 左上闭合
                        ]
                        
                        marker_id = self.progress_canvas.create_polygon(
                            gourd_points, fill="#ffeb3b", outline="#fbc02d", width=1
                        )
                        
                        # 在葫芦形中心添加标记名称
                        text_id = self.progress_canvas.create_text(
                            marker_pos_x, marker_top - 10,
                            text=marker_name, fill="#000000", font=('Arial', 10, 'bold')
                        )
                        
                        # 为标记添加标签
                        self.progress_canvas.addtag_withtag("yellow_marker", marker_id)
                        self.progress_canvas.addtag_withtag("yellow_marker", text_id)
                        
                        # 格式化时间显示
                        marker_time_str = self.format_time(marker_time)
                        
                        # 绑定点击事件和鼠标移入移出事件
                        try:
                            self.progress_canvas.tag_bind(marker_id, "<Button-1>", lambda e, i=idx: self.jump_to_marker_and_play(i))
                            self.progress_canvas.tag_bind(text_id, "<Button-1>", lambda e, i=idx: self.jump_to_marker_and_play(i))
                            self.progress_canvas.tag_bind(marker_id, "<Enter>", lambda e, t=marker_time_str, x=marker_pos_x: self.show_marker_time_tooltip(t, x))
                            self.progress_canvas.tag_bind(text_id, "<Enter>", lambda e, t=marker_time_str, x=marker_pos_x: self.show_marker_time_tooltip(t, x))
                            self.progress_canvas.tag_bind(marker_id, "<Leave>", lambda e: self.hide_marker_time_tooltip())
                            self.progress_canvas.tag_bind(text_id, "<Leave>", lambda e: self.hide_marker_time_tooltip())
                        except Exception as ex:
                            print(f"[调试] 标记绑定失败: {ex}")
                            pass
        
        # 在非录制模式下，确保黄色标记在最上层（但在剪辑标记之下）
        if not self.recording and self.markers:
            self.progress_canvas.tag_raise("yellow_marker")
        
        # 绘制截取视频标识
        if self.clip_mode and self.video_duration > 0:
            total_duration = self.video_duration
            if total_duration > 0:
                # 计算开始和结束位置，考虑留白
                start_pos = padding + (self.clip_start / total_duration) * usable_width
                end_pos = padding + (self.clip_end / total_duration) * usable_width
                
                # 绘制截取区域
                if start_pos < end_pos:
                    self.clip_area_id = self.progress_canvas.create_rectangle(
                        start_pos, 0, end_pos, height,
                        fill="#33691e", outline="", stipple="gray50"
                    )
                
                # 绘制开始截取标识（长方形样式，在画布内）
                rect_width = 50
                rect_height = 120  # 长方形长度，确保在画布内显示
                # 计算开始标记的位置，确保在画布范围内
                start_rect_x1 = max(0, start_pos - rect_width // 2)
                start_rect_x2 = min(width, start_pos + rect_width // 2)
                # 绘制长方形（在画布上方，中心与进度条位置对齐）
                self.clip_start_id = self.progress_canvas.create_rectangle(
                    start_rect_x1, 10,
                    start_rect_x2, 10 + rect_height,
                    fill="#4caf50", outline="#388e3c", width=2
                )
                # 添加截取入点文本（竖向排列4个字，居中显示）
                start_text_id = self.progress_canvas.create_text(
                    start_pos, 10 + rect_height // 2,
                    text="截\n取\n入\n点",
                    fill="white",
                    font=("Arial", 10, "bold"),
                    anchor=tk.CENTER
                )
                # 创建一个透明的大区域用于点击，确保在画布范围内
                start_hitbox_x1 = max(0, start_pos - 30)
                start_hitbox_x2 = min(width, start_pos + 30)
                start_hitbox_id = self.progress_canvas.create_rectangle(
                    start_hitbox_x1, 5, start_hitbox_x2, 15 + rect_height,
                    fill="", outline=""
                )
                
                # 为开始标记的所有元素添加标签
                self.progress_canvas.addtag_withtag("clip_start", self.clip_start_id)
                self.progress_canvas.addtag_withtag("clip_start", start_text_id)
                self.progress_canvas.addtag_withtag("clip_start", start_hitbox_id)
                
                # 绘制结束截取标识（长方形样式，在画布内）
                # 计算结束标记的位置，确保在画布范围内
                end_rect_x1 = max(0, end_pos - rect_width // 2)
                end_rect_x2 = min(width, end_pos + rect_width // 2)
                # 绘制长方形（在画布上方，中心与进度条位置对齐）
                self.clip_end_id = self.progress_canvas.create_rectangle(
                    end_rect_x1, 10,
                    end_rect_x2, 10 + rect_height,
                    fill="#f44336", outline="#d32f2f", width=2
                )
                # 添加截取出点文本（竖向排列4个字，居中显示）
                end_text_id = self.progress_canvas.create_text(
                    end_pos, 10 + rect_height // 2,
                    text="截\n取\n出\n点",
                    fill="white",
                    font=("Arial", 10, "bold"),
                    anchor=tk.CENTER
                )
                # 创建一个透明的大区域用于点击，确保在画布范围内
                end_hitbox_x1 = max(0, end_pos - 30)
                end_hitbox_x2 = min(width, end_pos + 30)
                end_hitbox_id = self.progress_canvas.create_rectangle(
                    end_hitbox_x1, 5, end_hitbox_x2, 15 + rect_height,
                    fill="", outline=""
                )
                
                # 为结束标记的所有元素添加标签
                self.progress_canvas.addtag_withtag("clip_end", self.clip_end_id)
                self.progress_canvas.addtag_withtag("clip_end", end_text_id)
                self.progress_canvas.addtag_withtag("clip_end", end_hitbox_id)
                
                # 绑定拖动事件
                try:
                    # 为开始标记标签绑定事件
                    self.progress_canvas.tag_bind("clip_start", "<Button-1>", self.on_clip_start_click)
                    self.progress_canvas.tag_bind("clip_start", "<B1-Motion>", self.on_clip_start_drag)
                    self.progress_canvas.tag_bind("clip_start", "<ButtonRelease-1>", self.on_clip_release)
                    
                    # 为结束标记标签绑定事件
                    self.progress_canvas.tag_bind("clip_end", "<Button-1>", self.on_clip_end_click)
                    self.progress_canvas.tag_bind("clip_end", "<B1-Motion>", self.on_clip_end_drag)
                    self.progress_canvas.tag_bind("clip_end", "<ButtonRelease-1>", self.on_clip_release)
                    
                    # 为整个画布添加全局事件绑定，确保剪辑模式下的点击事件被正确处理
                    self.progress_canvas.bind("<Button-1>", self.on_canvas_click)
                    self.progress_canvas.bind("<B1-Motion>", self.on_canvas_drag)
                    self.progress_canvas.bind("<ButtonRelease-1>", self.on_canvas_release)
                    
                    print("剪辑标记事件绑定成功")
                except Exception as e:
                    print(f"事件绑定失败: {e}")
                
                # 设置层级置顶（剪辑标记在所有元素之上，包括黄色标记和进度旋钮）
                self.progress_canvas.tag_raise("clip_start")
                self.progress_canvas.tag_raise("clip_end")
                self.progress_canvas.tag_raise("yellow_marker")
        
        # 最后绘制进度旋钮，确保它在所有元素之上
        knob_x = padding + progress_width
        knob_id = self.progress_canvas.create_oval(
            knob_x - 8, progress_bar_y - 5, knob_x + 8, progress_bar_y + progress_bar_height + 5,
            fill="#fff", outline="#ddd", width=2
        )
        # 为旋钮添加标签并设置为置顶
        self.progress_canvas.addtag_withtag("progress_knob", knob_id)
        self.progress_canvas.tag_raise("progress_knob")
        
        # 同步更新缩略功能区的时间轴
        self.update_mini_progress_bar()
    
    def update_progress(self):
        while not self.stop_update:
            if self.recording:
                # 录屏时：根据实际录制帧数计算时间，确保与视频时长一致
                if not self.paused:
                    # 使用实际录制帧数计算时间
                    self.current_time = self.recorded_frames / 10.0
            elif self.video_duration > 0 and self.video_playing and not self.progress_bar_dragging:
                if not self.video_paused:
                    self.current_time += 0.1
                    if self.current_time >= self.video_duration:
                        self.current_time = self.video_duration
                        self.video_playing = False
                        self.play_btn.config(state=tk.NORMAL)
                        self.pause_video_btn.config(state=tk.DISABLED)
            if self.recording or self.video_duration > 0:
                if not self.progress_bar_dragging:
                    self.update_progress_bar()
                self.update_time_label()
            time.sleep(0.1)
    
    def update_time_label(self):
        current = self.format_time(self.current_time)
        if self.recording:
            total = "--:--"
        else:
            total = self.format_time(self.video_duration)
        self.time_label.config(text=f"{current} / {total}")
        # 更新提示信息
        self.update_hints()
    
    def mark_progress(self, source="main"):
        # 如果正在录屏且处于暂停状态，不允许标记进度
        if self.recording and self.paused:
            if hasattr(self, 'mark_btn_tooltip') and self.mark_btn_tooltip:
                try:
                    self.mark_btn_tooltip.destroy()
                except:
                    pass
            if hasattr(self, 'mini_window') and self.mini_window:
                self.show_notification("暂停状态下无法标记进度", is_weak=True, parent=self.mini_window)
            else:
                self.show_notification("暂停状态下无法标记进度", is_weak=True)
            return

        # 如果没有在录屏且没有打开视频文件，提示用户
        if not self.recording and not self.video_file:
            self.show_notification("请先开始录屏或打开视频文件", is_weak=True)
            return

        if self.recording or self.video_file:
            marker_time = self.current_time
            print(f"[调试] 添加标记: 时间={marker_time:.2f}")
            marker = {
                "id": self.marker_count + 1, "name": str(self.marker_count + 1), "time": marker_time, "note": ""
            }
            self.markers.append(marker)
            self.marker_count += 1
            print(f"[调试] 标记已添加，当前标记数量={len(self.markers)}")
            for i, m in enumerate(self.markers):
                print(f"[调试] 标记{i}: 时间={m['time']:.2f}")
            self.update_progress_bar()
            # 显示在缩略功能区下方（如果有）
            if hasattr(self, 'mini_window') and self.mini_window:
                self.show_notification(f"已完成标记（第{self.marker_count}个）", is_weak=True, parent=self.mini_window)
            else:
                self.show_notification(f"已完成标记（第{self.marker_count}个）", is_weak=True)
            # 保存标记到文件
            self.save_markers_to_file()

    def start_clip(self):
        if self.video_file and self.video_duration > 0:
            self.clip_mode = True
            self.clip_start = 0
            self.clip_end = self.video_duration
            # 切换按钮为取消截取
            self.clip_btn.config(text="取消截取", command=self.cancel_clip, state=tk.NORMAL)
            self.finish_clip_btn.config(state=tk.NORMAL)
            self.update_progress_bar()

    def cancel_clip(self):
        """取消截取视频"""
        self.clip_mode = False
        # 恢复按钮为截取视频
        self.clip_btn.config(text="截取视频", command=self.start_clip, state=tk.NORMAL)
        self.finish_clip_btn.config(state=tk.DISABLED)
        self.update_progress_bar()
    
    def finish_clip(self):
        """完成截取视频"""
        if self.clip_mode:
            if self.clip_start < self.clip_end:
                clip = {
                    "id": len(self.clips) + 1,
                    "start": self.clip_start,
                    "end": self.clip_end,
                    "duration": self.clip_end - self.clip_start
                }
                self.clips.append(clip)
                
                # 保存剪辑到"截取视频"文件夹
                if self.video_file:
                    try:
                        # 构建剪辑保存路径 - 为每个片段创建单独文件夹
                        # 检查片段是否有自定义名称
                        if 'name' in clip and clip['name']:
                            clip_folder_name = clip['name']
                        else:
                            # 获取当前视频的文件名（不含路径和后缀）
                            video_filename = ""
                            if self.video_file:
                                basename = os.path.basename(self.video_file)
                                video_filename = os.path.splitext(basename)[0] + "_"
                            # 使用与显示名称一致的格式
                            clip_folder_name = f"{video_filename}片段_{clip['id']}"
                        
                        # 创建片段文件夹
                        clip_folder = os.path.join(os.path.dirname(self.video_file), self.clip_dir, clip_folder_name)
                        if not os.path.exists(clip_folder):
                            os.makedirs(clip_folder)
                        
                        # 片段视频文件路径
                        clip_path = os.path.join(clip_folder, "clip.avi")
                        
                        # 获取视频信息并使用FFmpeg快速裁剪
                        cap = cv2.VideoCapture(self.video_file)
                        if cap.isOpened():
                            fps = cap.get(cv2.CAP_PROP_FPS)
                            width = int(cap.get(cv2.CAP_PROP_FRAME_WIDTH))
                            height = int(cap.get(cv2.CAP_PROP_FRAME_HEIGHT))
                            cap.release()
                            
                            # 计算开始时间和持续时间
                            start_time = clip["start"]
                            duration = clip["end"] - clip["start"]
                            
                            clip_saved = False
                            # 使用FFmpeg快速裁剪（速度比cv2逐帧处理快10-50倍）
                            if IMAGEIO_FFMPEG_AVAILABLE:
                                try:
                                    ffmpeg_exe = imageio_ffmpeg.get_ffmpeg_exe()
                                    
                                    # FFmpeg命令：-ss指定开始时间，-t指定持续时间，-c copy表示直接复制流不重新编码
                                    cmd = [
                                        ffmpeg_exe,
                                        '-y',  # 覆盖输出文件
                                        '-ss', str(start_time),
                                        '-i', self.video_file,
                                        '-t', str(duration),
                                        '-c', 'copy',  # 直接复制，不重新编码，速度最快
                                        '-avoid_negative_ts', 'make_zero',
                                        clip_path
                                    ]
                                    
                                    result = subprocess.run(cmd, capture_output=True, text=True)
                                    if result.returncode != 0:
                                        print(f"FFmpeg copy模式失败，错误信息: {result.stderr}")
                                        # 如果copy模式失败，尝试重新编码模式
                                        cmd_reencode = [
                                            ffmpeg_exe,
                                            '-y',
                                            '-ss', str(start_time),
                                            '-i', self.video_file,
                                            '-t', str(duration),
                                            '-c:v', 'libx264',  # 使用H.264编码
                                            '-preset', 'ultrafast',  # 最快预设
                                            '-c:a', 'aac',
                                            clip_path
                                        ]
                                        result = subprocess.run(cmd_reencode, capture_output=True, text=True)
                                        if result.returncode != 0:
                                            print(f"FFmpeg reencode模式也失败: {result.stderr}")
                                    
                                    if result.returncode == 0:
                                        print(f"剪辑已保存到: {clip_path}")
                                        clip_saved = True
                                    else:
                                        print("FFmpeg处理失败，尝试使用cv2方式")
                                        self.extract_clip_with_cv2(clip, clip_path, fps, width, height)
                                        if os.path.exists(clip_path):
                                            clip_saved = True
                                except Exception as ffmpeg_err:
                                    print(f"FFmpeg裁剪失败，回退到cv2方式: {ffmpeg_err}")
                                    self.extract_clip_with_cv2(clip, clip_path, fps, width, height)
                                    if os.path.exists(clip_path):
                                        clip_saved = True
                            else:
                                # 没有FFmpeg，使用cv2方式
                                self.extract_clip_with_cv2(clip, clip_path, fps, width, height)
                                if os.path.exists(clip_path):
                                    clip_saved = True
                            
                            # 只有在视频片段成功保存后才创建签名文件
                            if clip_saved:
                                # 保存片段信息到video_clips字典
                                if self.video_file not in self.video_clips:
                                    self.video_clips[self.video_file] = []
                                existing_clip = next((c for c in self.video_clips[self.video_file] if c['id'] == clip['id']), None)
                                if existing_clip:
                                    existing_clip.update(clip)
                                else:
                                    self.video_clips[self.video_file].append(clip.copy())
                                
                                # 创建片段工具签名文件
                                self.create_clip_signature(clip_folder, clip)
                            else:
                                print("警告：视频片段保存失败，未创建签名文件")
                        else:
                            print("无法打开原始视频文件")
                    except Exception as e:
                        print(f"保存剪辑时出错: {e}")
                
                self.update_clips()
                self.show_notification(f"已完成截取，片段时长：{self.format_time(clip['duration'])}", is_weak=True)
            self.clip_mode = False
            # 恢复按钮为截取视频
            self.clip_btn.config(text="截取视频", command=self.start_clip, state=tk.NORMAL)
            self.finish_clip_btn.config(state=tk.DISABLED)
            self.update_progress_bar()
    
    def on_clip_start_click(self, event):
        print(f"开始标记点击事件触发，坐标: ({event.x}, {event.y})")
        self.dragging_clip_start = True
    
    def on_clip_start_drag(self, event):
        if self.dragging_clip_start and self.clip_mode and self.video_duration > 0:
            width = self.progress_canvas.winfo_width()
            if width > 0:
                padding = 20
                usable_width = width - 2 * padding
                # 计算新的开始位置，考虑留白
                if event.x < padding:
                    new_pos = padding
                elif event.x > width - padding:
                    new_pos = width - padding
                else:
                    new_pos = event.x
                new_time = ((new_pos - padding) / usable_width) * self.video_duration
                # 确保开始位置小于结束位置
                if new_time < self.clip_end:
                    self.clip_start = new_time
                    self.update_progress_bar()
                    # 更新提示信息
                    self.update_hints()
    
    def on_clip_end_click(self, event):
        print(f"结束标记点击事件触发，坐标: ({event.x}, {event.y})")
        self.dragging_clip_end = True
    
    def on_clip_end_drag(self, event):
        if self.dragging_clip_end and self.clip_mode and self.video_duration > 0:
            width = self.progress_canvas.winfo_width()
            if width > 0:
                padding = 20
                usable_width = width - 2 * padding
                # 计算新的结束位置，考虑留白
                if event.x < padding:
                    new_pos = padding
                elif event.x > width - padding:
                    new_pos = width - padding
                else:
                    new_pos = event.x
                new_time = ((new_pos - padding) / usable_width) * self.video_duration
                # 确保结束位置大于开始位置
                if new_time > self.clip_start:
                    self.clip_end = new_time
                    self.update_progress_bar()
                    # 更新提示信息
                    self.update_hints()
    
    def on_clip_release(self, event):
        print(f"释放事件触发，坐标: ({event.x}, {event.y})")
        self.dragging_clip_start = False
        self.dragging_clip_end = False
    
    def on_canvas_click(self, event):
        if self.clip_mode and self.video_duration > 0:
            width = self.progress_canvas.winfo_width()
            if width > 0:
                # 计算点击位置对应的时间
                click_time = (event.x / width) * self.video_duration
                
                # 检查点击位置是否靠近开始标记
                start_pos = (self.clip_start / self.video_duration) * width
                end_pos = (self.clip_end / self.video_duration) * width
                
                # 定义点击区域的阈值
                threshold = 30
                
                if abs(event.x - start_pos) <= threshold:
                    print(f"点击了开始标记附近，坐标: ({event.x}, {event.y})")
                    self.dragging_clip_start = True
                elif abs(event.x - end_pos) <= threshold:
                    print(f"点击了结束标记附近，坐标: ({event.x}, {event.y})")
                    self.dragging_clip_end = True
    
    def on_canvas_drag(self, event):
        if self.clip_mode and self.video_duration > 0:
            width = self.progress_canvas.winfo_width()
            if width > 0:
                padding = 20
                usable_width = width - 2 * padding
                # 计算拖动位置对应的时间，限制在画布范围内
                if event.x < padding:
                    new_pos = padding
                elif event.x > width - padding:
                    new_pos = width - padding
                else:
                    new_pos = event.x
                drag_time = ((new_pos - padding) / usable_width) * self.video_duration
                
                if self.dragging_clip_start and drag_time < self.clip_end:
                    self.clip_start = drag_time
                    self.update_progress_bar()
                elif self.dragging_clip_end and drag_time > self.clip_start:
                    self.clip_end = drag_time
                    self.update_progress_bar()
    
    def on_canvas_release(self, event):
        if self.clip_mode:
            self.dragging_clip_start = False
            self.dragging_clip_end = False
    
    def jump_to_marker(self, index):
        if 0 <= index < len(self.markers):
            self.current_time = self.markers[index]["time"]
            if self.video_duration > 0:
                self.update_progress_bar()
                self.update_time_label()
            self.current_marker_index = index
    
    def jump_to_marker_and_play(self, index):
        if self.video_playing:
            self.pause_video()
            if self.video_thread:
                self.video_thread.join(timeout=0.5)
        self.jump_to_marker(index)
        if self.video_file:
            self.play_video()
    
    def update_clips(self):
        print(f"\n=== update_clips 被调用 ===")
        print(f"self.clips 长度: {len(self.clips)}")
        print(f"self.clips 内容: {self.clips}")
        print(f"clip_listbox 是否存在: {hasattr(self, 'clip_listbox')}")
        
        self.clip_listbox.delete(0, tk.END)
        
        # 获取当前视频的文件名（不含路径和后缀）
        video_filename = ""
        if self.video_file:
            basename = os.path.basename(self.video_file)
            video_filename = os.path.splitext(basename)[0] + "_"
        
        # 先收集所有片段信息，找出最长的名称
        clip_items = []
        for clip in self.clips:
            start = self.format_time(clip["start"])
            end = self.format_time(clip["end"])
            
            # 获取截取时入点和出点间的标记进度的名称
            clip_start = clip["start"]
            clip_end = clip["end"]
            
            # 查找在入点和出点之间的标记
            markers_in_range = [m for m in self.markers if clip_start <= m["time"] <= clip_end]
            
            if len(markers_in_range) >= 1:
                # 如果有>=1个标记，取靠左（时间最小）的标记名称
                left_marker = min(markers_in_range, key=lambda m: m["time"])
                marker_name = left_marker.get("name", "")
            else:
                # 如果有<1个标记（即0个），填充为空
                marker_name = ""
            
            # 使用自定义名称（如果存在），否则使用默认格式
            if 'name' in clip and clip['name']:
                # 格式：{自定义名称}: {开始时间} - {结束时间} ({标记名称})
                item = f"{clip['name']}: {start} - {end} ({marker_name})"
            else:
                # 格式：{视频文件名}_{片段 id}: {开始时间} - {结束时间} ({标记名称})
                item = f"{video_filename}片段 {clip['id']}: {start} - {end} ({marker_name})"
            clip_items.append(item)
            print(f"插入片段: {item}")
            self.clip_listbox.insert(tk.END, item)
        
        print(f"插入完成后 listbox size: {self.clip_listbox.size()}")
        
        # 计算最长的片段名称长度，并设置列表框宽度
        if clip_items:
            max_length = max(len(item) for item in clip_items)
            # 加上5个字符的宽度
            self.clip_listbox.configure(width=max_length + 5)
        else:
            # 默认宽度
            self.clip_listbox.configure(width=35)
        
        # 默认选中第一条数据
        if self.clips:
            self.clip_listbox.selection_set(0)
        else:
            self.clip_listbox.selection_clear(0, tk.END)
    
    def play_selected_clip(self):
        selected = self.clip_listbox.curselection()
        if selected:
            clip = self.clips[selected[0]]
            # 注释掉原来的内部播放器代码
            # self.play_clip(clip)
            
            # 改为打开系统播放器
            import os
            clip_folder = clip.get('folder_name', f"recording_{self.current_session_dir.split(os.sep)[-1]}_片段_{clip['id']}")
            clip_path = os.path.join(self.current_session_dir, "截取视频", clip_folder, "clip.avi")
            
            if os.path.exists(clip_path):
                print(f"打开系统播放器播放: {clip_path}")
                os.startfile(clip_path)
            else:
                self.show_notification("片段文件不存在", is_weak=True)
                print(f"片段文件不存在: {clip_path}")
    
    def play_clip(self, clip):
        if self.video_file:
            print("\n=== 开始播放剪辑 ===")
            print(f"剪辑信息: 开始时间={clip['start']:.2f}秒, 结束时间={clip['end']:.2f}秒, 时长={clip['duration']:.2f}秒")
            
            # 检查剪辑时间范围是否有效
            if clip['start'] >= clip['end']:
                print("[错误] 剪辑时间范围无效: 开始时间 >= 结束时间")
                messagebox.showerror("错误", "剪辑时间范围无效")
                return
            
            # 检查视频文件是否存在
            if not os.path.exists(self.video_file):
                print(f"[错误] 视频文件不存在: {self.video_file}")
                messagebox.showerror("错误", "视频文件不存在")
                return
            
            print(f"视频文件: {self.video_file}")
            print(f"文件大小: {os.path.getsize(self.video_file):,} 字节")
            
            # 停止当前可能正在播放的视频
            print(f"当前 stop_video 值: {self.stop_video}")
            self.stop_video = True
            print(f"设置 stop_video 为 True")
            if self.video_thread:
                print("等待当前视频线程结束...")
                self.video_thread.join(timeout=1)
                print("当前视频线程已结束")
            # 重置 stop_video 为 False，为新的剪辑播放做准备
            self.stop_video = False
            print(f"重置 stop_video 为 False")
            # 启动剪辑播放线程
            print("启动剪辑播放线程...")
            self.video_thread = threading.Thread(target=self.play_clip_thread, args=(clip,))
            self.video_thread.daemon = True
            self.video_thread.start()
            print("剪辑播放线程已启动")
    
    def play_clip_thread(self, clip):
        print("\n=== 剪辑播放线程开始 ===")
        print(f"线程ID: {threading.get_ident()}")
        cap = cv2.VideoCapture(self.video_file)
        if not cap.isOpened():
            print("[错误] 无法打开视频文件")
            messagebox.showerror("错误", "无法打开视频文件")
            return
        
        # 获取视频信息
        fps = cap.get(cv2.CAP_PROP_FPS)
        total_frames = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
        print(f"视频信息: FPS={fps:.1f}, 总帧数={total_frames}")
        
        start_frame = int(clip["start"] * fps)
        end_frame = int(clip["end"] * fps)
        print(f"剪辑范围: 开始帧={start_frame}, 结束帧={end_frame}")
        
        # 设置起始帧
        cap.set(cv2.CAP_PROP_POS_FRAMES, start_frame)
        current_frame = start_frame
        print(f"当前帧设置为: {current_frame}")
        
        # 计算弹窗大小为当前工具窗口的70%
        root_width = self.root.winfo_width()
        root_height = self.root.winfo_height()
        if root_width == 0 or root_height == 0:
            # 如果窗口还未初始化，使用默认值
            root_width = 1200
            root_height = 800
        window_width = int(root_width * 0.7)
        window_height = int(root_height * 0.7)
        print(f"弹窗大小: {window_width}x{window_height}")
        
        # 创建播放窗口
        clip_window = tk.Toplevel(self.root)
        clip_window.title(f"播放片段 {clip['id']}")
        clip_window.geometry(f"{window_width}x{window_height}")
        clip_window.resizable(True, True)
        
        # 创建画布
        clip_canvas = tk.Canvas(clip_window, bg="black")
        clip_canvas.pack(fill=tk.BOTH, expand=True)
        
        # 创建控制按钮框架
        control_frame = tk.Frame(clip_window, bg="#333")
        control_frame.pack(fill=tk.X, side=tk.BOTTOM, pady=5)
        
        # 播放按钮
        def play_video():
            nonlocal is_playing, current_frame, frame_count
            if not is_playing:
                is_playing = True
                play_btn.config(state=tk.DISABLED)
                pause_btn.config(state=tk.NORMAL)
            # 如果已经播放到结尾，重新开始播放
            if current_frame > end_frame:
                current_frame = start_frame
                frame_count = 0
                cap.set(cv2.CAP_PROP_POS_FRAMES, start_frame)
                # 重置时间和进度条
                time_var.set(f"00:00 / {format_time(total_clip_frames / fps)}")
                width = progress_canvas.winfo_width()
                if width > 0:
                    progress_canvas.delete('all')
                    progress_canvas.create_rectangle(0, 0, width, 20, fill="#555", outline="")
                    progress_canvas.create_oval(-6, 2, 6, 18, fill="#fff", outline="#ddd", width=2)
        
        # 暂停按钮
        def pause_video():
            nonlocal is_playing
            if is_playing:
                is_playing = False
                play_btn.config(state=tk.NORMAL)
                pause_btn.config(state=tk.DISABLED)
        
        is_playing = True
        play_btn = tk.Button(control_frame, text="播放", command=play_video, padx=10, pady=5)
        play_btn.pack(side=tk.LEFT, padx=5)
        play_btn.config(state=tk.DISABLED)  # 初始状态下播放中，禁用播放按钮
        
        pause_btn = tk.Button(control_frame, text="暂停", command=pause_video, padx=10, pady=5)
        pause_btn.pack(side=tk.LEFT, padx=5)
        pause_btn.config(state=tk.NORMAL)  # 初始状态下播放中，启用暂停按钮
        
        # 关闭按钮（隐藏）
        def close_window():
            nonlocal stop_playback
            stop_playback = True
            cap.release()
            clip_window.destroy()
        
        # 隐藏关闭按钮，通过窗口关闭按钮关闭
        clip_window.protocol("WM_DELETE_WINDOW", close_window)
        
        # 时间轴和进度条（与主页面保持一致）
        time_frame = tk.Frame(control_frame, bg="#333")
        time_frame.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=10)
        
        # 时间标签
        time_var = tk.StringVar()
        time_var.set("00:00 / 00:00")
        time_label = tk.Label(time_frame, textvariable=time_var, fg="white", bg="#333")
        time_label.pack(side=tk.RIGHT, padx=10)
        
        # 进度条画布
        progress_canvas = tk.Canvas(time_frame, height=20, bg="#333", highlightthickness=0)
        progress_canvas.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=10)
        
        # 进度条拖动状态
        progress_bar_dragging = False
        
        # 进度条点击事件
        def on_progress_click(event):
            nonlocal progress_bar_dragging, current_frame
            progress_bar_dragging = True
            width = progress_canvas.winfo_width()
            if width > 0:
                position = max(0, min(1, event.x / width))
                # 计算新的帧位置
                new_frame = int(start_frame + position * total_clip_frames)
                new_frame = max(start_frame, min(end_frame, new_frame))
                # 设置视频位置
                cap.set(cv2.CAP_PROP_POS_FRAMES, new_frame)
                current_frame = new_frame
                # 更新进度条显示
                update_progress_display(position)
        
        # 进度条拖动事件
        def on_progress_drag(event):
            nonlocal progress_bar_dragging, current_frame
            if progress_bar_dragging:
                width = progress_canvas.winfo_width()
                if width > 0:
                    position = max(0, min(1, event.x / width))
                    # 计算新的帧位置
                    new_frame = int(start_frame + position * total_clip_frames)
                    new_frame = max(start_frame, min(end_frame, new_frame))
                    # 设置视频位置
                    cap.set(cv2.CAP_PROP_POS_FRAMES, new_frame)
                    current_frame = new_frame
                    # 更新进度条显示
                    update_progress_display(position)
        
        # 更新进度条显示函数
        def update_progress_display(position):
            width = progress_canvas.winfo_width()
            if width > 0:
                progress_canvas.delete('all')
                # 绘制背景
                progress_canvas.create_rectangle(0, 0, width, 20, fill="#555", outline="")
                # 绘制进度
                progress_x = int(width * position)
                progress_canvas.create_rectangle(0, 0, progress_x, 20, fill="#4caf50", outline="")
                # 绘制旋钮
                knob_x = int(width * position)
                progress_canvas.create_oval(knob_x - 8, 2, knob_x + 8, 18, fill="#fff", outline="#ddd", width=2)
                # 更新时间标签
                current_time_seconds = (position * total_clip_frames) / fps
                time_var.set(f"{format_time(current_time_seconds)} / {format_time(total_clip_frames / fps)}")
        
        # 进度条释放事件
        def on_progress_release(event):
            nonlocal progress_bar_dragging
            progress_bar_dragging = False
        
        # 绑定进度条事件
        progress_canvas.bind("<Button-1>", on_progress_click)
        progress_canvas.bind("<B1-Motion>", on_progress_drag)
        progress_canvas.bind("<ButtonRelease-1>", on_progress_release)
        
        # 窗口关闭事件
        clip_window.protocol("WM_DELETE_WINDOW", close_window)
        print("播放窗口已创建")
        
        # 确保 stop_video 为 False
        self.stop_video = False
        stop_playback = False
        print(f"线程内设置 stop_video 为: {self.stop_video}")
        
        # 计算总帧数，用于调试
        total_clip_frames = end_frame - start_frame + 1
        print(f"剪辑总帧数: {total_clip_frames}")
        
        # 格式化时间函数（支持小时）
        def format_time(seconds):
            hours = int(seconds // 3600)
            mins = int((seconds % 3600) // 60)
            secs = int(seconds % 60)
            if hours > 0:
                return f"{hours:02d}:{mins:02d}:{secs:02d}"
            else:
                return f"{mins:02d}:{secs:02d}"
        
        # 检查循环条件
        print(f"循环前检查: current_frame={current_frame}, end_frame={end_frame}, stop_video={self.stop_video}")
        print(f"循环条件: {current_frame <= end_frame} and {not self.stop_video} and {not stop_playback} = {current_frame <= end_frame and not self.stop_video and not stop_playback}")
        
        frame_count = 0
        # 主循环：保持线程活跃，支持重复播放
        while not self.stop_video and not stop_playback:
            # 检查是否需要重新开始播放
            if is_playing:
                # 如果已经播放到结尾，停止播放
                if current_frame > end_frame:
                    is_playing = False
                    play_btn.config(state=tk.NORMAL)  # 启用播放按钮
                    pause_btn.config(state=tk.DISABLED)  # 禁用暂停按钮
                    # 重置到开始位置
                    current_frame = start_frame
                    frame_count = 0
                    cap.set(cv2.CAP_PROP_POS_FRAMES, start_frame)
                    # 重置时间和进度条
                    time_var.set(f"00:00 / {format_time(total_clip_frames / fps)}")
                    width = progress_canvas.winfo_width()
                    if width > 0:
                        progress_canvas.delete('all')
                        progress_canvas.create_rectangle(0, 0, width, 20, fill="#555", outline="")
                        progress_canvas.create_oval(-6, 2, 6, 18, fill="#fff", outline="#ddd", width=2)
                    # 跳过本次循环，等待用户点击播放
                    clip_window.update()
                    time.sleep(0.1)
                    continue
                
                # 检查是否到达结束帧
                if current_frame == end_frame:
                    # 播放完最后一帧后停止
                    is_playing = False
                    play_btn.config(state=tk.NORMAL)  # 启用播放按钮
                    pause_btn.config(state=tk.DISABLED)  # 禁用暂停按钮
                    # 重置到开始位置
                    current_frame = start_frame
                    frame_count = 0
                    cap.set(cv2.CAP_PROP_POS_FRAMES, start_frame)
                    # 重置时间和进度条
                    time_var.set(f"00:00 / {format_time(total_clip_frames / fps)}")
                    width = progress_canvas.winfo_width()
                    if width > 0:
                        progress_canvas.delete('all')
                        progress_canvas.create_rectangle(0, 0, width, 20, fill="#555", outline="")
                        progress_canvas.create_oval(-6, 2, 6, 18, fill="#fff", outline="#ddd", width=2)
                    # 跳过本次循环，等待用户点击播放
                    clip_window.update()
                    time.sleep(0.1)
                    continue
                
                print(f"\n循环开始: 第{frame_count}次迭代")
                print(f"当前状态: current_frame={current_frame}, end_frame={end_frame}, stop_video={self.stop_video}, stop_playback={stop_playback}")
                
                # 读取帧
                ret, frame = cap.read()
                print(f"读取帧: ret={ret}")
                
                if not ret:
                    print(f"[警告] 读取帧失败，当前帧: {current_frame}")
                    # 停止播放
                    is_playing = False
                    play_btn.config(state=tk.NORMAL)  # 启用播放按钮
                    pause_btn.config(state=tk.DISABLED)  # 禁用暂停按钮
                    # 重置到开始位置
                    current_frame = start_frame
                    frame_count = 0
                    cap.set(cv2.CAP_PROP_POS_FRAMES, start_frame)
                    # 重置时间和进度条
                    time_var.set(f"00:00 / {format_time(total_clip_frames / fps)}")
                    width = progress_canvas.winfo_width()
                    if width > 0:
                        progress_canvas.delete('all')
                        progress_canvas.create_rectangle(0, 0, width, 20, fill="#555", outline="")
                        progress_canvas.create_oval(-6, 2, 6, 18, fill="#fff", outline="#ddd", width=2)
                    # 跳过本次循环，等待用户点击播放
                    clip_window.update()
                    time.sleep(0.1)
                    continue
                
                # 转换颜色并调整大小以适应窗口
                frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                # 获取画布大小
                canvas_width = clip_canvas.winfo_width()
                canvas_height = clip_canvas.winfo_height()
                if canvas_width > 0 and canvas_height > 0:
                    # 调整帧大小
                    img = Image.fromarray(frame)
                    img = img.resize((canvas_width, canvas_height), Image.LANCZOS)
                    imgtk = ImageTk.PhotoImage(image=img)
                    clip_canvas.create_image(0, 0, anchor=tk.NW, image=imgtk)
                    clip_canvas.imgtk = imgtk
                
                clip_window.update()
                print("帧已显示")
                
                # 延时
                time.sleep(1/fps)  # 使用视频的实际帧率
                current_frame += 1
                frame_count += 1
                
                # 计算当前时间和总时间
                current_time = (current_frame - start_frame) / fps
                total_time = total_clip_frames / fps
                
                # 更新时间标签
                time_var.set(f"{format_time(current_time)} / {format_time(total_time)}")
                
                # 更新进度条
                width = progress_canvas.winfo_width()
                if width > 0:
                    progress = (current_frame - start_frame) / total_clip_frames
                    progress_width = int(width * progress)
                    # 清除旧的进度条
                    progress_canvas.delete('all')
                    # 绘制背景
                    progress_canvas.create_rectangle(0, 0, width, 20, fill="#555", outline="")
                    # 绘制进度
                    progress_canvas.create_rectangle(0, 0, progress_width, 20, fill="#4CAF50", outline="")
                    # 绘制旋钮
                    knob_x = progress_width
                    progress_canvas.create_oval(knob_x - 6, 2, knob_x + 6, 18, fill="#fff", outline="#ddd", width=2)
                
                # 每5帧打印一次进度
                if frame_count % 5 == 0:
                    print(f"播放进度: 帧 {current_frame}/{end_frame} ({(current_frame-start_frame)/total_clip_frames*100:.1f}%)")
            else:
                # 暂停状态或等待播放
                clip_window.update()
                time.sleep(0.1)
        
        print(f"\n=== 循环结束 ===")
        print(f"最终状态: current_frame={current_frame}, end_frame={end_frame}, stop_video={self.stop_video}, stop_playback={stop_playback}")
        print(f"播放了 {frame_count} 帧")
        
        # 清理
        print("释放视频捕获")
        cap.release()
        print("销毁播放窗口")
        clip_window.destroy()
        print("剪辑播放线程结束")
    
    def on_clip_window_close(self, window, cap):
        """旧的窗口关闭处理函数（保留以确保兼容性）"""
        self.stop_video = True
        try:
            cap.release()
        except:
            pass
        try:
            window.destroy()
        except:
            pass
    
    def delete_selected_clip(self):
        selected = self.clip_listbox.curselection()
        if selected:
            # 显示二次确认弹窗
            confirm = messagebox.askyesno("确认删除", "确定要删除选中的片段吗？")
            if confirm:
                # 从列表中删除片段
                clip_index = selected[0]
                clip = self.clips[clip_index]
                clip_id = clip.get('id', clip_index + 1)
                
                # 删除对应的文件
                if self.current_session_dir:
                    clip_dir = os.path.join(self.current_session_dir, self.clip_dir)
                    # 构建文件路径
                    if 'name' in clip and clip['name']:
                        clip_file = os.path.join(clip_dir, f"{clip['name']}.avi")
                    else:
                        # 获取当前视频的文件名（不含路径和后缀）
                        video_filename = ""
                        if self.video_file:
                            basename = os.path.basename(self.video_file)
                            video_filename = os.path.splitext(basename)[0] + "_"
                        clip_file = os.path.join(clip_dir, f"{video_filename}片段 {clip_id}.avi")
                    
                    # 删除文件
                    if os.path.exists(clip_file):
                        try:
                            os.remove(clip_file)
                            print(f"删除片段文件: {clip_file}")
                        except Exception as e:
                            print(f"删除文件失败: {e}")
                
                # 从内存中删除片段
                self.clips.pop(clip_index)
                # 更新片段列表
                self.update_clips()
                # 显示删除成功通知
                self.show_notification("片段删除成功", is_weak=True)
    
    def play_video(self):
        if self.video_file:
            # 如果处于暂停状态，只取消暂停，继续播放（不从头开始）
            if self.video_playing and self.video_paused:
                self.video_paused = False
                self.play_btn.config(state=tk.DISABLED)
                self.pause_video_btn.config(state=tk.NORMAL)
                self.status_label.config(text="状态: 播放中", fg="#4CAF50")
            else:
                # 停止状态或正在播放：从头开始播放
                self.stop_video = True
                if self.video_thread:
                    self.video_thread.join(timeout=1)
                self.video_playing = True
                self.video_paused = False
                self.play_btn.config(state=tk.DISABLED)
                self.pause_video_btn.config(state=tk.NORMAL)
                self.status_label.config(text="状态: 播放中", fg="#4CAF50")
                self.video_thread = threading.Thread(target=self.play_video_thread)
                self.video_thread.daemon = True
                self.video_thread.start()
    
    def play_video_thread(self):
        print("\n=== 主页面视频播放线程开始 ===")
        self.video_capture = cv2.VideoCapture(self.video_file)
        if not self.video_capture.isOpened():
            messagebox.showerror("错误", "无法打开视频文件")
            self.video_playing = False
            self.play_btn.config(state=tk.NORMAL)
            self.pause_video_btn.config(state=tk.DISABLED)
            return
        self.stop_video = False
        frame_count = 0
        print(f"开始播放视频: {self.video_file}")
        
        # 检查是否处于截取视频状态
        if self.clip_mode and self.video_duration > 0:
            # 设置视频起始位置为入点
            start_pos_msec = self.clip_start * 1000
            with self.video_lock:
                self.video_capture.set(cv2.CAP_PROP_POS_MSEC, start_pos_msec)
            print(f"截取模式：从 {self.clip_start:.2f} 秒开始播放，到 {self.clip_end:.2f} 秒结束")
        
        while self.video_playing and not self.stop_video:
            if not self.video_paused:
                with self.video_lock:
                    ret, frame = self.video_capture.read()
                    if not ret:
                        print(f"[主页面] 读取帧失败，播放结束")
                        break
                    # 获取当前播放位置（毫秒）并更新 current_time
                    current_pos_msec = self.video_capture.get(cv2.CAP_PROP_POS_MSEC)
                # 只在不在拖动进度条时更新 current_time
                if not self.progress_bar_dragging:
                    self.current_time = current_pos_msec / 1000.0
                
                # 检查是否处于截取视频状态，如果是，检查是否到达出点
                if self.clip_mode and self.video_duration > 0:
                    if self.current_time > self.clip_end:
                        print(f"[主页面] 到达出点 {self.clip_end:.2f} 秒，播放结束")
                        break
                
                frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                img = Image.fromarray(frame)
                # 缩放帧以适应canvas大小，保持宽高比
                canvas_width = self.canvas.winfo_width()
                canvas_height = self.canvas.winfo_height()
                if canvas_width > 0 and canvas_height > 0:
                    img_width, img_height = img.size
                    canvas_ratio = canvas_width / canvas_height
                    img_ratio = img_width / img_height
                    
                    if canvas_ratio > img_ratio:
                        # Canvas更宽，以高度为基准缩放
                        new_height = canvas_height
                        new_width = int(img_width * (canvas_height / img_height))
                    else:
                        # Canvas更高，以宽度为基准缩放
                        new_width = canvas_width
                        new_height = int(img_height * (canvas_width / img_width))
                    
                    img = img.resize((new_width, new_height), Image.LANCZOS)
                imgtk = ImageTk.PhotoImage(image=img)
                self.canvas.create_image(canvas_width // 2, canvas_height // 2, anchor=tk.CENTER, image=imgtk)
                self.canvas.imgtk = imgtk
                self.root.update()
                
                # 每10帧更新一次进度条，避免过于频繁的更新
                frame_count += 1
                if frame_count % 10 == 0:
                    self.update_progress_bar()
                    self.update_time_label()
                
                time.sleep(0.05)
            else:
                time.sleep(0.1)
        
        print(f"[主页面] 播放循环结束，frame_count={frame_count}")
        
        if self.video_capture:
            with self.video_lock:
                self.video_capture.release()
            self.video_capture = None
        self.video_playing = False
        self.play_btn.config(state=tk.NORMAL)
        self.pause_video_btn.config(state=tk.DISABLED)
        self.status_label.config(text="状态: 未播放", fg=self.secondary_text)
        # 播放结束时更新进度条到结束位置
        self.current_time = self.video_duration
        self.update_progress_bar()
        self.update_time_label()
        print("[主页面] 视频播放完成，状态已更新")
    
    def pause_video(self):
        self.video_paused = not self.video_paused
        if self.video_paused:
            # 暂停状态：启用播放按钮，禁用暂停按钮
            self.play_btn.config(state=tk.NORMAL)
            self.pause_video_btn.config(state=tk.DISABLED)
            self.status_label.config(text="状态: 暂停中", fg="#9E9E9E")
        else:
            # 取消暂停：禁用播放按钮，启用暂停按钮
            self.play_btn.config(state=tk.DISABLED)
            self.pause_video_btn.config(state=tk.NORMAL)
            self.status_label.config(text="状态: 播放中", fg="#4CAF50")
    
    def on_progress_click(self, event):
        if self.video_duration > 0:
            # 检查是否点击了剪辑标记区域
            if not self.clip_mode:
                self.progress_bar_dragging = True
                width = self.progress_canvas.winfo_width()
                if width > 0:
                    padding = 20
                    usable_width = width - 2 * padding
                    # 计算点击位置，考虑留白
                    if event.x < padding:
                        position = 0
                    elif event.x > width - padding:
                        position = 1
                    else:
                        position = (event.x - padding) / usable_width
                    self.current_time = position * self.video_duration
                    # 显示时间提示
                    self.show_time_tooltip(event.x, event.y, self.current_time)
                    self.update_progress_bar()
                    self.update_time_label()
            else:
                # 在剪辑模式下，不处理进度条点击，让剪辑标记的点击事件优先处理
                pass
    
    def on_progress_drag(self, event):
        if self.progress_bar_dragging and self.video_duration > 0:
            width = self.progress_canvas.winfo_width()
            if width > 0:
                padding = 20
                usable_width = width - 2 * padding
                # 计算拖动位置，考虑留白
                if event.x < padding:
                    position = 0
                elif event.x > width - padding:
                    position = 1
                else:
                    position = (event.x - padding) / usable_width
                self.current_time = position * self.video_duration
                # 显示时间提示
                self.show_time_tooltip(event.x, event.y, self.current_time)
                self.update_progress_bar()
                self.update_time_label()
                # 同步视频位置到拖动位置
                with self.video_lock:
                    if self.video_playing and self.video_capture:
                        self.video_capture.set(cv2.CAP_PROP_POS_MSEC, self.current_time * 1000)
    
    def on_progress_release(self, event):
        if self.progress_bar_dragging:
            self.progress_bar_dragging = False
            with self.video_lock:
                if self.video_playing and self.video_capture:
                    self.video_capture.set(cv2.CAP_PROP_POS_MSEC, self.current_time * 1000)
            # 销毁时间提示窗口
            if hasattr(self, 'time_tooltip') and self.time_tooltip:
                try:
                    self.time_tooltip.destroy()
                except:
                    pass
            # 更新提示信息
            self.update_hints()
    
    def update_hints(self):
        """更新常驻提示信息"""
        # 格式化时间（支持小时）
        def format_time(seconds):
            if seconds < 0:
                seconds = 0
            if self.video_duration > 0 and seconds > self.video_duration:
                seconds = self.video_duration
            hours = int(seconds // 3600)
            mins = int((seconds % 3600) // 60)
            secs = int(seconds % 60)
            if hours > 0:
                return f"{hours:02d}:{mins:02d}:{secs:02d}"
            else:
                return f"{mins:02d}:{secs:02d}"
        
        # 更新进度旋钮提示
        knob_time = format_time(self.current_time)
        if hasattr(self, 'knob_hint_label'):
            self.knob_hint_label.config(text=f"进度: {knob_time}")
        if hasattr(self, 'knob_hint_entry'):
            self.knob_hint_entry.delete(0, tk.END)
            self.knob_hint_entry.insert(0, knob_time)
        
        # 更新入点提示
        in_point_time = format_time(self.clip_start)
        if hasattr(self, 'in_point_hint_label'):
            self.in_point_hint_label.config(text=f"截取入点: {in_point_time}")
        if hasattr(self, 'in_point_hint_entry'):
            self.in_point_hint_entry.delete(0, tk.END)
            self.in_point_hint_entry.insert(0, in_point_time)
        
        # 更新出点提示
        out_point_time = format_time(self.clip_end)
        if hasattr(self, 'out_point_hint_label'):
            self.out_point_hint_label.config(text=f"截取出点: {out_point_time}")
        if hasattr(self, 'out_point_hint_entry'):
            self.out_point_hint_entry.delete(0, tk.END)
            self.out_point_hint_entry.insert(0, out_point_time)
    
    def on_knob_hint_change(self, event):
        """进度旋钮提示变化"""
        try:
            # 解析时间输入（支持HH:MM:SS和MM:SS格式）
            time_str = self.knob_hint_entry.get().strip()
            if ':' in time_str:
                parts = time_str.split(':')
                if len(parts) == 3:
                    # HH:MM:SS格式
                    hours, mins, secs = int(parts[0]), int(parts[1]), int(parts[2])
                    new_time = hours * 3600 + mins * 60 + secs
                else:
                    # MM:SS格式
                    mins, secs = int(parts[0]), int(parts[1])
                    new_time = mins * 60 + secs
            else:
                new_time = int(time_str)
            
            # 验证时间范围
            if new_time < 0:
                new_time = 0
            if self.video_duration > 0 and new_time > self.video_duration:
                new_time = self.video_duration
            
            # 更新当前时间
            self.current_time = new_time
            self.update_progress_bar()
            self.update_hints()
            
            # 更新时间标签
            current_time_str = self.format_time(self.current_time)
            total_time_str = self.format_time(self.video_duration)
            self.time_label.config(text=f"{current_time_str} / {total_time_str}")
            
        except ValueError:
            pass
    
    def on_in_point_hint_change(self, event):
        """入点提示变化"""
        try:
            # 解析时间输入（支持HH:MM:SS和MM:SS格式）
            time_str = self.in_point_hint_entry.get().strip()
            if ':' in time_str:
                parts = time_str.split(':')
                if len(parts) == 3:
                    # HH:MM:SS格式
                    hours, mins, secs = int(parts[0]), int(parts[1]), int(parts[2])
                    new_time = hours * 3600 + mins * 60 + secs
                else:
                    # MM:SS格式
                    mins, secs = int(parts[0]), int(parts[1])
                    new_time = mins * 60 + secs
            else:
                new_time = int(time_str)
            
            # 验证时间范围
            if new_time < 0:
                new_time = 0
            if self.video_duration > 0 and new_time > self.video_duration:
                new_time = self.video_duration
            if new_time > self.clip_end:
                new_time = self.clip_end
            
            # 更新入点
            self.clip_start = new_time
            self.update_progress_bar()
            self.update_hints()
            
        except ValueError:
            pass
    
    def on_out_point_hint_change(self, event):
        """出点提示变化"""
        try:
            # 解析时间输入（支持HH:MM:SS和MM:SS格式）
            time_str = self.out_point_hint_entry.get().strip()
            if ':' in time_str:
                parts = time_str.split(':')
                if len(parts) == 3:
                    # HH:MM:SS格式
                    hours, mins, secs = int(parts[0]), int(parts[1]), int(parts[2])
                    new_time = hours * 3600 + mins * 60 + secs
                else:
                    # MM:SS格式
                    mins, secs = int(parts[0]), int(parts[1])
                    new_time = mins * 60 + secs
            else:
                new_time = int(time_str)
            
            # 验证时间范围
            if new_time < 0:
                new_time = 0
            if self.video_duration > 0 and new_time > self.video_duration:
                new_time = self.video_duration
            if new_time < self.clip_start:
                new_time = self.clip_start
            
            # 更新出点
            self.clip_end = new_time
            self.update_progress_bar()
            self.update_hints()
            
        except ValueError:
            pass

    def show_login_tip(self, message, is_success=True):
        """在登录弹窗标题区域显示黑色框提示"""
        if hasattr(self, 'login_tip_label') and self.login_tip_label:
            color = "#4CAF50" if is_success else "#ff6b6b"
            self.login_tip_label.config(text=message, fg="#ffffff", bg="#1a1a1a")
            # 2秒后恢复透明状态
            self.login_dialog.after(2000, lambda: self.login_tip_label.config(text=" ", fg="#4CAF50", bg="#4CAF50"))
    
    def show_notification(self, message, is_weak=False, parent=None):
        if is_weak:
            # 弱提示，自动消失
            weak_notification = tk.Toplevel(self.root if parent is None else parent)
            weak_notification.title("通知")
            weak_notification.geometry("260x80")
            weak_notification.transient(self.root)
            weak_notification.attributes('-topmost', True)
            weak_notification.configure(bg=self.card_bg)
            
            # 添加边框效果
            weak_notification.overrideredirect(True)
            
            # 创建圆角效果的画布
            canvas = tk.Canvas(weak_notification, width=260, height=80, bg=self.card_bg, 
                            highlightthickness=1, highlightbackground=self.border_color)
            canvas.pack()
            
            # 绘制圆角背景
            def create_roundrectangle(canvas, x1, y1, x2, y2, radius, **kwargs):
                points = [
                    x1+radius, y1,
                    x2-radius, y1,
                    x2, y1+radius,
                    x2, y2-radius,
                    x2-radius, y2,
                    x1+radius, y2,
                    x1, y2-radius,
                    x1, y1+radius
                ]
                return canvas.create_polygon(points, **kwargs)
            
            create_roundrectangle(canvas, 0, 0, 260, 80, 8, fill=self.light_bg, outline=self.accent_color)
            
            # 添加文本
            canvas.create_text(130, 40, text=message, fill=self.text_color, font=('Arial', 10, 'bold'))
            
            # 计算位置，让通知显示在指定父窗口的上方
            screen_width = self.root.winfo_screenwidth()
            screen_height = self.root.winfo_screenheight()
            
            if parent is not None:
                parent.update_idletasks()
                parent_x = parent.winfo_x()
                parent_y = parent.winfo_y()
                parent_width = parent.winfo_width()
                # 在父窗口（缩略功能区）下方显示
                x = parent_x + (parent_width - 260) // 2  # 水平居中于弹窗
                y = parent_y + parent.winfo_height() + 10  # 在弹窗下方显示
                
                # 确保通知在屏幕内
                if x < 10:
                    x = 10
                if x + 260 > screen_width:
                    x = screen_width - 270
                if y + 80 > screen_height:
                    y = screen_height - 90
            else:
                # 如果没有指定父窗口，但有缩略功能区窗口，显示在缩略功能区下方
                if hasattr(self, 'mini_window') and self.mini_window:
                    self.mini_window.update_idletasks()
                    mini_x = self.mini_window.winfo_x()
                    mini_y = self.mini_window.winfo_y()
                    mini_width = self.mini_window.winfo_width()
                    x = mini_x + (mini_width - 260) // 2  # 水平居中于缩略功能区
                    y = mini_y + self.mini_window.winfo_height() + 10  # 在缩略功能区下方显示
                    
                    # 确保通知在屏幕内
                    if x < 10:
                        x = 10
                    if x + 260 > screen_width:
                        x = screen_width - 270
                    if y + 80 > screen_height:
                        y = screen_height - 90
                else:
                    # 默认位置：屏幕右下角
                    x = screen_width - 280
                    y = screen_height - 100
            weak_notification.geometry(f"260x80+{x}+{y}")
            
            # 显示通知
            weak_notification.deiconify()
            weak_notification.lift()  # 将窗口提升到最顶层
            
            # 2秒后自动销毁
            self.root.after(2000, lambda: weak_notification.destroy())
        else:
            # 强提示，需要用户确认
            self.notification_label.config(text=message)
            self.notification.deiconify()
    
    def open_marker_edit(self):
        if 0 <= self.current_marker_index < len(self.markers):
            marker = self.markers[self.current_marker_index]
            self.marker_name_var.set(marker.get("name", str(marker["id"])))
            self.marker_note_var.set(marker.get("note", ""))
            self.marker_edit_window.deiconify()
    
    def save_marker_edit(self):
        if 0 <= self.current_marker_index < len(self.markers):
            marker = self.markers[self.current_marker_index]
            marker["name"] = self.marker_name_var.get() or str(marker["id"])
            marker["note"] = self.marker_note_var.get()
            self.marker_edit_window.withdraw()
            self.notification.withdraw()
            # 保存标记到文件
            self.save_markers_to_file()

    def show_record_history(self):
        """显示录制记录"""
        # 创建录制记录窗口
        history_window = tk.Toplevel(self.root)
        history_window.title("录制记录")
        history_window.geometry("800x450")  # 增大高度，确保能显示按钮
        history_window.configure(bg="#1a1a1a")
        history_window.resizable(True, True)
        
        
        # 标题
        title_label = tk.Label(history_window, text="录制记录", 
                             font=('Arial', 14, 'bold'),
                             bg="#1a1a1a", fg="#ffffff")
        title_label.pack(pady=10)
        
        # 记录列表 - 使用Treeview实现表格
        list_frame = tk.Frame(history_window, bg="#1a1a1a")
        list_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        # 创建Treeview
        columns = ('录制时间', '记录内容')
        history_tree = ttk.Treeview(list_frame, columns=columns, show='headings', selectmode='browse')
        history_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        # 设置列
        history_tree.heading('录制时间', text='录制时间')
        history_tree.heading('记录内容', text='记录内容')
        history_tree.column('录制时间', width=180, anchor='center')
        history_tree.column('记录内容', width=580, anchor='w')
        
        # 设置样式
        style = ttk.Style()
        style.configure("Treeview", 
                       background="#252525",
                       foreground="#ffffff",
                       fieldbackground="#252525",
                       rowheight=28)
        style.configure("Treeview.Heading",
                       background=self.card_bg,
                       foreground="#ffffff",
                       font=('Arial', 10, 'bold'))
        style.map("Treeview", 
                 background=[('selected', '#3a3a3a')],
                 foreground=[('selected', '#ffffff')])
        
        # 添加滚动条
        scrollbar = ttk.Scrollbar(list_frame, orient="vertical", command=history_tree.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        history_tree.configure(yscrollcommand=scrollbar.set)
        
        # 存储会话路径，用于打开功能
        session_paths = []
        
        # 扫描recordings目录
        if os.path.exists(self.recordings_dir):
            sessions = os.listdir(self.recordings_dir)
            # 按时间戳排序，从远到近
            sessions.sort(reverse=False)
            
            for session in sessions:
                session_path = os.path.join(self.recordings_dir, session)
                if os.path.isdir(session_path):
                    # 先验证是否为工具产生的会话
                    is_valid, _ = self.is_valid_tool_session(session_path)
                    if not is_valid:
                        continue
                    
                    # 查找主视频文件（排除截取视频文件夹中的文件）
                    clip_dir = os.path.join(session_path, self.clip_dir)
                    all_files = os.listdir(session_path)
                    video_files = [f for f in all_files if f.endswith('.avi') and os.path.join(session_path, f) != clip_dir]
                    # 如果有截取视频文件夹，也排除其中的文件
                    if os.path.exists(clip_dir):
                        clip_avi_files = [f for f in os.listdir(clip_dir) if f.endswith('.avi')]
                        video_files = [f for f in video_files if f not in clip_avi_files]
                    
                    if video_files:
                        # 读取当前的实际文件名
                        current_filename = video_files[0]
                        
                        # 格式化录制时间：年月日时分秒
                        session_time = session.replace('_', '')
                        if len(session_time) >= 14:
                            formatted_time = f"{session_time[:4]}-{session_time[4:6]}-{session_time[6:8]} {session_time[8:10]}:{session_time[10:12]}:{session_time[12:14]}"
                        else:
                            formatted_time = session_time
                        
                        # 统计截取视频数量（新结构：每个片段一个文件夹）
                        clip_count = 0
                        if os.path.exists(clip_dir):
                            clip_folders = [f for f in os.listdir(clip_dir) if os.path.isdir(os.path.join(clip_dir, f))]
                            clip_count = len(clip_folders)
                        
                        # 添加到表格
                        record_content = f"主视频: {current_filename} - 截取: {clip_count}个"
                        history_tree.insert('', tk.END, values=(formatted_time, record_content))
                        session_paths.append(session_path)
        
        # 滚动到最下面（显示最新记录）
        if history_tree.get_children():
            history_tree.see(history_tree.get_children()[-1])
        
        # 打开按钮
        def open_selected_record():
            selected_item = history_tree.selection()
            if selected_item:
                # 获取选中的项
                item_index = history_tree.index(selected_item[0])
                if item_index < len(session_paths):
                    session_path = session_paths[item_index]
                    
                    if os.path.exists(session_path):
                        # 双重验证：确保是工具产生的视频
                        is_valid, error_msg = self.is_valid_tool_session(session_path)
                        if not is_valid:
                            messagebox.showerror(
                                "无法打开此视频",
                                "该视频不是由本工具录制产生的。\n\n录制记录功能仅支持打开本工具录制的视频文件。"
                            )
                            return
                        
                        # 查找主视频文件（排除截取视频文件夹中的文件）
                        clip_dir = os.path.join(session_path, self.clip_dir)
                        all_files = os.listdir(session_path)
                        video_files = [f for f in all_files if f.endswith('.avi') and os.path.join(session_path, f) != clip_dir]
                        # 如果有截取视频文件夹，也排除其中的文件
                        if os.path.exists(clip_dir):
                            clip_avi_files = [f for f in os.listdir(clip_dir) if f.endswith('.avi')]
                            video_files = [f for f in video_files if f not in clip_avi_files]
                        
                        if video_files:
                            # 打开视频文件
                            video_file = os.path.join(session_path, video_files[0])
                            self.video_file = video_file
                            self.current_session_dir = session_path  # 更新当前会话目录
                            print(f"打开录制记录，会话目录: {self.current_session_dir}")
                            print(f"视频文件: {self.video_file}")
                            # 检查截取视频文件夹
                            clip_dir = os.path.join(self.current_session_dir, self.clip_dir)
                            print(f"截取视频文件夹: {clip_dir}")
                            if os.path.exists(clip_dir):
                                clip_files = [f for f in os.listdir(clip_dir) if f.endswith('.avi')]
                                print(f"截取视频文件夹中存在 {len(clip_files)} 个文件")
                            else:
                                print("截取视频文件夹不存在")
                            
                            # 加载视频信息
                            self.show_first_frame()
                            
                            # 关闭历史窗口
                            history_window.destroy()
        
        # 按钮框架
        button_frame = tk.Frame(history_window, bg="#1a1a1a")
        button_frame.pack(fill=tk.X, padx=10, pady=10)
        
        open_btn = ttk.Button(button_frame, text="打开选中记录", command=open_selected_record, style='Accent.TButton')
        open_btn.pack(side=tk.LEFT, padx=5)
        
        close_btn = ttk.Button(button_frame, text="关闭", command=history_window.destroy, style='Custom.TButton')
        close_btn.pack(side=tk.RIGHT, padx=5)
    
    def show_video_library(self):
        """显示/隐藏视频资料库"""
        # 检查视频资料库是否正在显示
        if self.library_frame.winfo_ismapped():
            # 如果正在显示，则隐藏
            self.hide_video_library()
        else:
            # 如果没有显示，则显示
            # 隐藏视频片段面板
            self.right_frame.pack_forget()
            # 显示视频资料库面板
            self.library_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(10, 0))
            # 初始化文件夹结构
            self.init_folder_structure()
    
    def hide_video_library(self):
        """隐藏视频资料库"""
        # 隐藏视频资料库面板
        self.library_frame.pack_forget()
        # 显示视频片段面板
        self.right_frame.pack(side=tk.RIGHT, fill=tk.Y)
        self.right_frame.configure(width=self.right_panel_width)
    
    def init_folder_structure(self):
        """初始化文件夹结构"""
        # 清空树状结构
        for item in self.folder_tree.get_children():
            self.folder_tree.delete(item)
        
        # 添加根节点
        root_id = self.folder_tree.insert('', tk.END, text="视频资料库", open=True)
        
        # 递归添加目录结构
        if os.path.exists(self.video_library_dir):
            self._add_folder_children(root_id, self.video_library_dir)
        
        # 重置搜索
        if hasattr(self, 'search_var'):
            self.search_var.set("")
            self.search_files()
    
    def _add_folder_children(self, parent_id, parent_path):
        """递归添加文件夹和文件子节点"""
        try:
            for item in os.listdir(parent_path):
                item_path = os.path.join(parent_path, item)
                if os.path.isdir(item_path):
                    # 检查当前子文件夹是否有子文件夹
                    child_subdirs = [subitem for subitem in os.listdir(item_path) if os.path.isdir(os.path.join(item_path, subitem))]
                    # 如果有子文件夹则展开，否则收起（只有视频文件时收起）
                    is_expand = len(child_subdirs) > 0
                    folder_id = self.folder_tree.insert(parent_id, tk.END, text="📂 " + item, values=[item_path], open=is_expand)
                    # 递归添加子节点
                    self._add_folder_children(folder_id, item_path)
                else:
                    # 添加文件节点（带彩色图标）
                    self.folder_tree.insert(parent_id, tk.END, text=item, image=self.file_icon, values=[item_path], open=False)
        except PermissionError:
            print(f"无法访问: {parent_path}")
    
    def show_folder_structure(self, event=None):
        """显示文件夹层级结构"""
        self.init_folder_structure()
    
    def search_files(self, event=None):
        """搜索文件和文件夹"""
        keyword = self.library_search_var.get().strip()
        
        # 重置目录树样式
        for item in self.folder_tree.get_children(''):
            self._reset_tree_item_style(item)
        
        if not keyword:
            # 如果没有关键词，清空统计信息
            self.search_stats_label.config(text="")
            return
        
        # 搜索文件和文件夹
        results = []
        folder_count = 0
        file_count = 0
        
        if os.path.exists(self.video_library_dir):
            for root, dirs, files in os.walk(self.video_library_dir):
                # 搜索文件夹
                for dir_name in dirs:
                    if keyword in dir_name:
                        results.append((os.path.join(root, dir_name), "文件夹"))
                        folder_count += 1
                # 搜索文件
                for file_name in files:
                    if keyword in file_name:
                        results.append((os.path.join(root, file_name), "文件"))
                        file_count += 1
        
        # 高亮显示匹配的结果
        for path, type_ in results:
            self._highlight_tree_item(path)
        
        # 显示搜索统计信息
        total_count = folder_count + file_count
        if total_count > 0:
            self.search_stats_label.config(
                text=f"找到 {total_count} 个结果：{folder_count} 个文件夹，{file_count} 个文件"
            )
        else:
            self.search_stats_label.config(text="没有找到匹配的结果")
    
    def _reset_tree_item_style(self, item):
        """重置树状结构项的样式"""
        # 重置当前项
        self.folder_tree.item(item, tags=())
        # 递归重置子项
        for child in self.folder_tree.get_children(item):
            self._reset_tree_item_style(child)
    
    def _highlight_tree_item(self, path):
        """高亮显示匹配的树状结构项"""
        # 从根节点开始查找
        root_item = self.folder_tree.get_children('')[0]
        self._find_and_highlight_item(root_item, path)    
    
    def _find_and_highlight_item(self, item, target_path):
        """递归查找并高亮匹配的树状结构项"""
        values = self.folder_tree.item(item, 'values')
        if values:
            item_path = values[0]
            if item_path == target_path:
                # 高亮显示匹配项
                self.folder_tree.item(item, tags=('highlight',))
                # 展开父节点
                parent = self.folder_tree.parent(item)
                while parent:
                    self.folder_tree.item(parent, open=True)
                    parent = self.folder_tree.parent(parent)
                return True
        
        # 递归搜索子项
        for child in self.folder_tree.get_children(item):
            if self._find_and_highlight_item(child, target_path):
                return True
        
        return False
    
    def open_selected_folder(self, event=None):
        """打开选中的文件夹"""
        selected_item = self.folder_tree.selection()
        if selected_item:
            item = selected_item[0]
            values = self.folder_tree.item(item, 'values')
            if values:
                folder_path = values[0]
                if os.path.exists(folder_path) and os.path.isdir(folder_path):
                    # 打开文件夹
                    if os.name == 'nt':
                        os.startfile(folder_path)
                    else:
                        subprocess.call(['open', folder_path])
    
    def open_current_folder(self):
        """打开当前选中的文件夹"""
        selected_item = self.folder_tree.selection()
        if selected_item:
            item = selected_item[0]
            values = self.folder_tree.item(item, 'values')
            if values:
                folder_path = values[0]
                if os.path.exists(folder_path):
                    if os.path.isdir(folder_path):
                        # 打开文件夹
                        if os.name == 'nt':
                            os.startfile(folder_path)
                        else:
                            subprocess.call(['open', folder_path])
                    else:
                        # 打开文件所在的文件夹
                        folder_path = os.path.dirname(folder_path)
                        if os.name == 'nt':
                            os.startfile(folder_path)
                        else:
                            subprocess.call(['open', folder_path])
        else:
            # 没有选中时打开视频资料库根目录
            if os.path.exists(self.video_library_dir):
                if os.name == 'nt':
                    os.startfile(self.video_library_dir)
                else:
                    subprocess.call(['open', self.video_library_dir])
    
    def create_new_folder(self):
        """新建文件夹"""
        # 获取当前选中的文件夹
        selected_item = self.folder_tree.selection()
        if not selected_item:
            # 默认在视频资料库目录下创建
            parent_path = self.video_library_dir
        else:
            item = selected_item[0]
            values = self.folder_tree.item(item, 'values')
            if values:
                parent_path = values[0]
            else:
                parent_path = self.video_library_dir
        
        # 创建文件夹名称输入窗口
        def create_folder():
            folder_name = folder_var.get().strip()
            if folder_name:
                folder_path = os.path.join(parent_path, folder_name)
                if not os.path.exists(folder_path):
                    try:
                        os.makedirs(folder_path)
                        # 更新文件夹结构
                        self.init_folder_structure()
                        self.show_notification("文件夹创建成功", is_weak=True)
                    except Exception as e:
                        messagebox.showerror("错误", f"创建文件夹失败: {str(e)}")
                else:
                    messagebox.showerror("错误", "文件夹已存在")
            window.destroy()
        
        window = tk.Toplevel(self.root)
        window.title("新建文件夹")
        window.geometry("300x150")
        window.resizable(False, False)
        window.attributes('-topmost', True)
        
        tk.Label(window, text="文件夹名称：").pack(pady=10)
        folder_var = tk.StringVar()
        entry = ttk.Entry(window, textvariable=folder_var)
        entry.pack(fill=tk.X, padx=20, pady=5)
        entry.focus()
        
        button_frame = tk.Frame(window)
        button_frame.pack(pady=10)
        ttk.Button(button_frame, text="确定", command=create_folder, style='Accent.TButton').pack(side=tk.LEFT, padx=10)
        ttk.Button(button_frame, text="取消", command=window.destroy, style='Custom.TButton').pack(side=tk.LEFT, padx=10)
    
    def import_file(self):
        """导入文件"""
        # 获取当前选中的文件夹
        selected_item = self.folder_tree.selection()
        if not selected_item:
            # 默认在视频资料库目录下创建
            parent_path = self.video_library_dir
        else:
            item = selected_item[0]
            values = self.folder_tree.item(item, 'values')
            if values:
                parent_path = values[0]
            else:
                parent_path = self.video_library_dir
        
        # 打开系统文件选择器
        file_paths = filedialog.askopenfilenames(
            title="选择要导入的文件",
            filetypes=[("视频文件", "*.avi *.mp4 *.mkv *.mov *.wmv"), ("所有文件", "*.*")]
        )
        
        if file_paths:
            success_count = 0
            fail_count = 0
            for src_path in file_paths:
                try:
                    file_name = os.path.basename(src_path)
                    dst_path = os.path.join(parent_path, file_name)
                    
                    # 如果目标文件已存在，生成新文件名
                    if os.path.exists(dst_path):
                        name, ext = os.path.splitext(file_name)
                        counter = 1
                        while os.path.exists(dst_path):
                            file_name = f"{name}_{counter}{ext}"
                            dst_path = os.path.join(parent_path, file_name)
                            counter += 1
                    
                    # 复制文件
                    import shutil
                    shutil.copy2(src_path, dst_path)
                    success_count += 1
                except Exception as e:
                    fail_count += 1
                    print(f"导入文件失败: {str(e)}")
            
            # 更新文件夹结构
            self.init_folder_structure()
            
            if success_count > 0:
                self.show_notification(f"成功导入 {success_count} 个文件", is_weak=True)
            if fail_count > 0:
                messagebox.showerror("错误", f"有 {fail_count} 个文件导入失败")
    
    def rename_selected_item(self):
        """重命名选中的项目"""
        # 检查是否选中了文件夹
        selected_folder = self.folder_tree.selection()
        if selected_folder:
            item = selected_folder[0]
            values = self.folder_tree.item(item, 'values')
            if values:
                old_path = values[0]
                old_name = os.path.basename(old_path)
                
                # 创建重命名窗口
                def rename_item():
                    new_name = name_var.get().strip()
                    if new_name and new_name != old_name:
                        new_path = os.path.join(os.path.dirname(old_path), new_name)
                        if not os.path.exists(new_path):
                            try:
                                os.rename(old_path, new_path)
                                # 更新文件夹结构
                                self.init_folder_structure()
                                self.show_notification("重命名成功", is_weak=True)
                            except Exception as e:
                                messagebox.showerror("错误", f"重命名失败: {str(e)}")
                        else:
                            messagebox.showerror("错误", "名称已存在")
                    window.destroy()
                
                window = tk.Toplevel(self.library_frame)
                window.title("重命名")
                window.geometry("600x300")
                window.resizable(False, False)
                window.attributes('-topmost', True)
                
                # 计算弹窗位置，使其显示在视频资料库模块内
                library_x = self.library_frame.winfo_x()
                library_y = self.library_frame.winfo_y()
                library_width = self.library_frame.winfo_width()
                library_height = self.library_frame.winfo_height()
                window_width = 600
                window_height = 300
                x = library_x + (library_width - window_width) // 2
                y = library_y + (library_height - window_height) // 2
                window.geometry(f"{window_width}x{window_height}+{x}+{y}")
                
                tk.Label(window, text="新名称：", font=('Arial', 12)).pack(pady=20)
                name_var = tk.StringVar(value=old_name)
                entry = ttk.Entry(window, textvariable=name_var, font=('Arial', 12))
                entry.pack(fill=tk.X, padx=40, pady=10)
                entry.select_range(0, tk.END)
                entry.focus()
                
                button_frame = tk.Frame(window)
                button_frame.pack(pady=30)
                ttk.Button(button_frame, text="确定", command=rename_item, style='Accent.TButton').pack(side=tk.LEFT, padx=20)
                ttk.Button(button_frame, text="取消", command=window.destroy, style='Custom.TButton').pack(side=tk.LEFT, padx=20)
            return
        
        # 检查是否选中了文件
        selected_file = self.file_listbox.curselection()
        if selected_file:
            index = selected_file[0]
            # 获取文件路径
            keyword = self.library_search_var.get().strip()
            if keyword:
                results = []
                if os.path.exists(self.video_library_dir):
                    for root, dirs, files in os.walk(self.video_library_dir):
                        for file_name in files:
                            if keyword in file_name:
                                results.append(os.path.join(root, file_name))
                if index < len(results):
                    old_path = results[index]
                    old_name = os.path.basename(old_path)
                    
                    # 创建重命名窗口
                    def rename_item():
                        new_name = name_var.get().strip()
                        if new_name and new_name != old_name:
                            if not new_name.endswith('.avi'):
                                new_name += '.avi'
                            new_path = os.path.join(os.path.dirname(old_path), new_name)
                            if not os.path.exists(new_path):
                                try:
                                    os.rename(old_path, new_path)
                                    # 更新文件列表
                                    self.search_files()
                                    self.show_notification("重命名成功", is_weak=True)
                                except Exception as e:
                                    messagebox.showerror("错误", f"重命名失败: {str(e)}")
                            else:
                                messagebox.showerror("错误", "名称已存在")
                        window.destroy()
                    
                    window = tk.Toplevel(self.library_frame)
                    window.title("重命名")
                    window.geometry("600x300")
                    window.resizable(False, False)
                    window.attributes('-topmost', True)
                    
                    # 计算弹窗位置，使其显示在视频资料库模块内
                    library_x = self.library_frame.winfo_x()
                    library_y = self.library_frame.winfo_y()
                    library_width = self.library_frame.winfo_width()
                    library_height = self.library_frame.winfo_height()
                    window_width = 600
                    window_height = 300
                    x = library_x + (library_width - window_width) // 2
                    y = library_y + (library_height - window_height) // 2
                    window.geometry(f"{window_width}x{window_height}+{x}+{y}")
                    
                    tk.Label(window, text="新名称：", font=('Arial', 12)).pack(pady=20)
                    name_var = tk.StringVar(value=old_name)
                    entry = ttk.Entry(window, textvariable=name_var, font=('Arial', 12))
                    entry.pack(fill=tk.X, padx=40, pady=10)
                    entry.select_range(0, tk.END)
                    entry.focus()
                    
                    button_frame = tk.Frame(window)
                    button_frame.pack(pady=30)
                    ttk.Button(button_frame, text="确定", command=rename_item, style='Accent.TButton').pack(side=tk.LEFT, padx=20)
                    ttk.Button(button_frame, text="取消", command=window.destroy, style='Custom.TButton').pack(side=tk.LEFT, padx=20)
    
    def delete_selected_item(self):
        """删除选中的项目"""
        # 检查是否选中了文件夹
        selected_folder = self.folder_tree.selection()
        if selected_folder:
            item = selected_folder[0]
            values = self.folder_tree.item(item, 'values')
            if values:
                path = values[0]
                confirm = messagebox.askyesno("确认删除", f"确定要删除 '{os.path.basename(path)}' 及其所有内容吗？")
                if confirm:
                    try:
                        import shutil
                        shutil.rmtree(path)
                        # 更新文件夹结构
                        self.init_folder_structure()
                        self.show_notification("删除成功", is_weak=True)
                    except Exception as e:
                        messagebox.showerror("错误", f"删除失败: {str(e)}")
            return
        
        # 检查是否选中了文件
        selected_file = self.file_listbox.curselection()
        if selected_file:
            index = selected_file[0]
            # 获取文件路径
            keyword = self.library_search_var.get().strip()
            if keyword:
                results = []
                if os.path.exists(self.video_library_dir):
                    for root, dirs, files in os.walk(self.video_library_dir):
                        for file_name in files:
                            if keyword in file_name:
                                results.append(os.path.join(root, file_name))
                if index < len(results):
                    path = results[index]
                    confirm = messagebox.askyesno("确认删除", f"确定要删除 '{os.path.basename(path)}' 吗？")
                    if confirm:
                        try:
                            os.remove(path)
                            # 更新文件列表
                            self.search_files()
                            self.show_notification("删除成功", is_weak=True)
                        except Exception as e:
                            messagebox.showerror("错误", f"删除失败: {str(e)}")

    def create_mini_control(self):
        """创建缩略功能区"""
        # 检查是否已存在缩略功能区
        if hasattr(self, 'mini_window') and self.mini_window:
            try:
                self.mini_window.destroy()
            except:
                pass
        
        # 创建缩略功能区窗口 - 作为完全独立的窗口
        self.mini_window = tk.Toplevel()  # 不指定master，使其成为独立窗口
        self.mini_window.title("录屏控制")
        self.mini_window.geometry("560x280")  # 增大窗口高度，从180增加到280，以容纳时间轴
        self.mini_window.attributes('-topmost', True)  # 始终显示在最前面
        self.mini_window.attributes('-toolwindow', True)  # 工具窗口风格
        self.mini_window.configure(bg="#1a1a1a")  # 直接使用颜色值，避免依赖主窗口
        # 添加阴影效果（通过边框实现）
        self.mini_window.configure(relief='flat', borderwidth=0)
        
        # 设置缩略功能区窗口的图标
        try:
            # 判断是否为 PyInstaller 打包环境
            if hasattr(sys, '_MEIPASS'):
                # 打包后：从临时目录加载
                icon_path = os.path.join(sys._MEIPASS, 'app_icon.ico')
            else:
                # 开发环境：从当前目录加载
                icon_path = os.path.join(os.path.dirname(__file__), 'app_icon.ico')
                
            if os.path.exists(icon_path):
                # 使用 PIL 加载图标并设置
                icon_image = Image.open(icon_path)
                icon_photo = ImageTk.PhotoImage(icon_image)
                self.mini_window.iconphoto(True, icon_photo)
                # 保留引用防止被垃圾回收
                self.mini_window.icon_image = icon_photo
        except Exception as e:
            print(f"设置缩略功能区窗口图标失败: {str(e)}")
        
        # 固定在屏幕顶部
        self.mini_window.geometry("560x280+50+50")
        
        # 创建时间轴容器
        self.mini_timeline_frame = tk.Frame(self.mini_window, bg="#1a1a1a")
        self.mini_timeline_frame.pack(fill=tk.X, pady=(10, 0), padx=20)
        
        # 创建缩略时间轴画布（与主页面时间轴保持一致的结构）
        self.mini_progress_canvas = tk.Canvas(self.mini_timeline_frame, height=120, bg="#333", 
                                              cursor="hand1", highlightthickness=0)
        self.mini_progress_canvas.pack(fill=tk.X)
        
        # 创建控制按钮
        button_frame = tk.Frame(self.mini_window, bg="#1a1a1a")
        button_frame.pack(fill=tk.X, pady=10, padx=20)  # 增加边距
        
        # 创建按钮
        self.mini_pause_btn = ttk.Button(button_frame, text="暂停录屏", command=self.pause_recording, width=10, takefocus=False)
        self.mini_pause_btn.pack(side=tk.LEFT, padx=10)  # 增加按钮间距
        
        self.mini_stop_btn = ttk.Button(button_frame, text="结束录屏", command=self.stop_recording, width=10)
        self.mini_stop_btn.pack(side=tk.LEFT, padx=10)
        
        # 标记进度按钮容器
        mark_btn_frame = tk.Frame(button_frame, bg="#1a1a1a")
        mark_btn_frame.pack(side=tk.LEFT, padx=10)
        
        # 修改标记进度按钮颜色，使其更突出
        self.mini_mark_btn = ttk.Button(mark_btn_frame, text="标记进度[空格]", 
                                       command=lambda: self.mark_progress(source="mini"), width=14, takefocus=False)
        # 配置按钮样式
        self.mini_mark_btn.configure(style='Accent.TButton')
        self.mini_mark_btn.pack(side=tk.LEFT)

        # 添加提示图形（圆形+？）
        help_canvas = tk.Canvas(mark_btn_frame, width=20, height=20, bg="#1a1a1a", highlightthickness=0)
        help_canvas.pack(side=tk.LEFT, padx=5)
        # 绘制圆形
        help_canvas.create_oval(2, 2, 18, 18, fill="#34a853", outline="white", width=2)
        # 绘制问号
        help_canvas.create_text(10, 12, text="?", fill="white", font=('Arial', 12, 'bold'))
        
        # 添加鼠标移入提示
        def show_mark_tooltip(event):
            # 销毁之前的提示窗口
            if hasattr(self, 'mark_btn_tooltip') and self.mark_btn_tooltip:
                try:
                    self.mark_btn_tooltip.destroy()
                except:
                    pass
            
            # 创建提示窗口
            tooltip = tk.Toplevel(self.mini_window)
            tooltip.title("")
            tooltip.geometry("320x80")
            tooltip.transient(self.mini_window)
            tooltip.overrideredirect(True)  # 无标题栏
            tooltip.attributes('-topmost', True)
            tooltip.attributes('-alpha', 0.9)  # 增加透明度，使其更明显
            tooltip.configure(bg="#333", relief="solid", borderwidth=2, bd=2)
            
            # 添加提示文本
            label = tk.Label(tooltip, 
                            text="标记进度后视频进度条上将同步产生黄色标记，便于定位标记片段", 
                            font=('Arial', 10), 
                            bg="#333", fg="#fff",
                            wraplength=300,  # 增加换行宽度
                            justify=tk.LEFT)  # 左对齐
            label.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
            
            # 计算位置 - 显示在按钮右侧，避免被遮挡
            x = mark_btn_frame.winfo_rootx() + mark_btn_frame.winfo_width() + 10
            y = mark_btn_frame.winfo_rooty()
            
            # 确保提示窗口在屏幕内
            screen_width = tooltip.winfo_screenwidth()
            screen_height = tooltip.winfo_screenheight()
            tooltip_width = 320
            tooltip_height = 80
            
            if x + tooltip_width > screen_width:
                x = screen_width - tooltip_width - 10
            if y + tooltip_height > screen_height:
                y = screen_height - tooltip_height - 10
            if y < 10:
                y = 10
            
            tooltip.geometry(f"{tooltip_width}x{tooltip_height}+{x}+{y}")
            
            # 强制更新窗口
            tooltip.update_idletasks()
            tooltip.lift()
            
            # 存储tooltip引用
            self.mark_btn_tooltip = tooltip
        
        def hide_mark_tooltip(event):
            if hasattr(self, 'mark_btn_tooltip') and self.mark_btn_tooltip:
                try:
                    self.mark_btn_tooltip.destroy()
                except:
                    pass
        
        # 绑定事件到整个标记进度按钮区域
        self.mini_mark_btn.bind("<Enter>", show_mark_tooltip)
        self.mini_mark_btn.bind("<Leave>", hide_mark_tooltip)
        help_canvas.bind("<Enter>", show_mark_tooltip)
        help_canvas.bind("<Leave>", hide_mark_tooltip)
        mark_btn_frame.bind("<Enter>", show_mark_tooltip)
        mark_btn_frame.bind("<Leave>", hide_mark_tooltip)
        
        # 绑定事件到整个缩略功能区窗口
        self.mini_window.bind("<Leave>", hide_mark_tooltip)
        
        # 添加状态标签
        self.mini_status_label = tk.Label(self.mini_window, text="录屏中...", 
                                        font=('Arial', 10),  # 增大字体
                                        bg="#1a1a1a", fg='green')
        self.mini_status_label.pack(pady=15)
        
        # 确保窗口显示在最前面
        self.mini_window.update_idletasks()  # 强制更新窗口任务
        self.mini_window.update()  # 强制更新窗口

        self.mini_window.lift()
        self.mini_window.focus_force()
        self.mini_window.deiconify()
        
        # 重写窗口关闭行为，确保点击关闭按钮时只是隐藏窗口，而不是销毁
        def on_close():
            self.mini_window.withdraw()
        
        self.mini_window.protocol("WM_DELETE_WINDOW", on_close)
        
        # 在缩略功能区窗口上也绑定空格键 - 标记进度
        def on_mini_space_key(event):
            # 如果正在录屏且处于暂停状态，不执行标记
            if self.recording and self.paused:
                return 'break'
            self.mark_progress(source="mini")
            return 'break'  # 阻止空格键的默认行为
        self.mini_window.bind('<space>', on_mini_space_key)
    
    def close_mini_control(self):
        """关闭缩略功能区"""
        if hasattr(self, 'mini_window') and self.mini_window:
            try:
                self.mini_window.destroy()
                self.mini_window = None
            except:
                pass
        if hasattr(self, 'mini_progress_canvas'):
            delattr(self, 'mini_progress_canvas')
    
    def update_mini_progress_bar(self):
        """更新缩略功能区的时间轴（与主页面时间轴同步）"""
        if not hasattr(self, 'mini_progress_canvas') or not self.mini_progress_canvas:
            return
        
        try:
            self.mini_progress_canvas.delete('all')
        except:
            return
            
        try:
            width = self.mini_progress_canvas.winfo_width()
            height = self.mini_progress_canvas.winfo_height()
        except:
            return
            
        if width == 0 or height == 0:
            return
        
        padding = 20
        usable_width = width - 2 * padding
        
        if self.video_duration > 0:
            progress = self.current_time / self.video_duration
        else:
            progress = 0
        
        self.mini_progress_canvas.create_rectangle(0, 0, width, height, fill="#333", outline="")
        
        progress_bar_y = height - 30
        progress_bar_height = 20
        progress_width = int(usable_width * progress)
        self.mini_progress_canvas.create_rectangle(padding, progress_bar_y, width - padding, progress_bar_y + progress_bar_height, fill="#444", outline="")
        self.mini_progress_canvas.create_rectangle(padding, progress_bar_y, padding + progress_width, progress_bar_y + progress_bar_height, fill="#4CAF50", outline="")
        
        if self.recording or self.video_duration > 0:
            max_marker_time = 0
            if self.recording:
                total_duration = self.current_time if self.current_time > 0 else 1
            else:
                max_marker_time = max([m["time"] for m in self.markers]) if self.markers else 0
                if self.video_duration <= 0 or self.video_duration < max_marker_time:
                    total_duration = max_marker_time if max_marker_time > 0 else 1
                else:
                    total_duration = self.video_duration
            
            if total_duration > 0:
                for idx, marker in enumerate(self.markers):
                    marker_time = marker["time"]
                    if marker_time <= total_duration:
                        marker_pos = padding + (marker_time / total_duration) * usable_width
                        marker_pos = max(padding + 4, min(width - padding - 4, marker_pos))
                        
                        marker_name = marker.get("name", str(idx + 1))
                        
                        marker_pos_x = marker_pos
                        marker_top = progress_bar_y - 20
                        
                        gourd_points = [
                            marker_pos_x - 20, marker_top - 25,
                            marker_pos_x - 10, marker_top - 30,
                            marker_pos_x + 10, marker_top - 30,
                            marker_pos_x + 20, marker_top - 25,
                            marker_pos_x + 20, marker_top - 10,
                            marker_pos_x + 14, marker_top - 5,
                            marker_pos_x + 14, marker_top + 5,
                            marker_pos_x + 6, marker_top + 10,
                            marker_pos_x, marker_top + 20,
                            marker_pos_x - 6, marker_top + 10,
                            marker_pos_x - 14, marker_top + 5,
                            marker_pos_x - 14, marker_top - 5,
                            marker_pos_x - 20, marker_top - 10,
                            marker_pos_x - 20, marker_top - 25,
                        ]
                        
                        marker_id = self.mini_progress_canvas.create_polygon(
                            gourd_points, fill="#ffeb3b", outline="#fbc02d", width=1
                        )
                        
                        text_id = self.mini_progress_canvas.create_text(
                            marker_pos_x, marker_top - 10,
                            text=marker_name, fill="#000000", font=('Arial', 10, 'bold')
                        )
        
        knob_x = padding + progress_width
        knob_id = self.mini_progress_canvas.create_oval(
            knob_x - 8, progress_bar_y - 5, knob_x + 8, progress_bar_y + progress_bar_height + 5,
            fill="#fff", outline="#ddd", width=2
        )
    
    def show_time_tooltip(self, x, y, time_seconds):
        """显示时间提示"""
        # 销毁之前的提示窗口
        if hasattr(self, 'time_tooltip') and self.time_tooltip:
            try:
                self.time_tooltip.destroy()
            except:
                pass
        
        # 创建新的提示窗口
        self.time_tooltip = tk.Toplevel(self.root)
        self.time_tooltip.title("")
        self.time_tooltip.geometry("80x30")
        self.time_tooltip.transient(self.root)
        self.time_tooltip.overrideredirect(True)  # 无标题栏
        self.time_tooltip.attributes('-topmost', True)
        self.time_tooltip.configure(bg="#333", relief="solid", borderwidth=1)
        
        # 格式化时间
        time_str = self.format_time(time_seconds)
        
        # 创建标签
        label = tk.Label(self.time_tooltip, text=time_str, 
                        font=('Arial', 10), 
                        bg="#333", fg="#fff")
        label.pack(fill=tk.BOTH, expand=True, padx=5, pady=3)
        
        # 计算提示窗口位置
        # 将坐标从canvas转换为屏幕坐标
        canvas_x = self.progress_canvas.winfo_rootx() + x
        canvas_y = self.progress_canvas.winfo_rooty() + y
        
        # 调整位置，使提示窗口显示在鼠标上方
        tooltip_width = 80
        tooltip_height = 30
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        
        # 确保提示窗口在屏幕内
        tooltip_x = canvas_x - tooltip_width // 2
        tooltip_y = canvas_y - tooltip_height - 10
        
        if tooltip_x < 0:
            tooltip_x = 0
        elif tooltip_x + tooltip_width > screen_width:
            tooltip_x = screen_width - tooltip_width
        
        if tooltip_y < 0:
            tooltip_y = canvas_y + 10
        
        self.time_tooltip.geometry(f"{tooltip_width}x{tooltip_height}+{tooltip_x}+{tooltip_y}")
    
    def save_recording_path(self):
        """保存录制路径到文件"""
        if self.video_file:
            try:
                with open(self.recordings_file, 'a', encoding='utf-8') as f:
                    f.write(f"{time.strftime('%Y-%m-%d %H:%M:%S')} - {self.video_file}\n")
            except Exception as e:
                print(f"保存录制路径失败: {e}")
    
    def show_marker_time_tooltip(self, time_str, x_pos):
        """显示标记时间提示"""
        self.hide_marker_time_tooltip()
        
        canvas_width = self.progress_canvas.winfo_width()
        tooltip_x = min(x_pos, canvas_width - 60)
        tooltip_x = max(10, tooltip_x)
        
        self.marker_tooltip = tk.Label(self.progress_canvas, text=time_str,
                                       bg="#ffeb3b", fg="#000000", font=('Arial', 10, 'bold'),
                                       padx=8, pady=4, relief='solid', bd=1)
        self.marker_tooltip.place(x=tooltip_x - 30, y=25)
    
    def hide_marker_time_tooltip(self):
        """隐藏标记时间提示"""
        if hasattr(self, 'marker_tooltip') and self.marker_tooltip:
            self.marker_tooltip.destroy()
            self.marker_tooltip = None
    
    def extract_clip_with_cv2(self, clip, clip_path, fps, width, height):
        """使用cv2方式提取视频片段（回退方案）"""
        cap = cv2.VideoCapture(self.video_file)
        if cap.isOpened():
            start_frame = int(clip["start"] * fps)
            end_frame = int(clip["end"] * fps)
            
            fourcc = cv2.VideoWriter_fourcc(*'XVID')
            out = cv2.VideoWriter(clip_path, fourcc, fps, (width, height))
            
            cap.set(cv2.CAP_PROP_POS_FRAMES, start_frame)
            
            current_frame = start_frame
            while current_frame <= end_frame and cap.isOpened():
                ret, frame = cap.read()
                if not ret:
                    break
                out.write(frame)
                current_frame += 1
            
            cap.release()
            out.release()
        else:
            print("无法打开原始视频文件")
    
    def format_time(self, seconds):
        """格式化时间（支持小时显示）"""
        hours = int(seconds // 3600)
        mins = int((seconds % 3600) // 60)
        secs = int(seconds % 60)
        if hours > 0:
            return f"{hours:02d}:{mins:02d}:{secs:02d}"
        else:
            return f"{mins:02d}:{secs:02d}"

if __name__ == "__main__":
    from PIL import Image, ImageTk
    root = tk.Tk()
    app = ScreenRecorder(root)
    root.mainloop()