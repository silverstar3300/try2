"""
智能垃圾分类系统 - Python 3.13.7 兼容版
作者：自动化学院 王语遥2025302186、谢雨珊2025312190
"""

# ================ 导入库 ================
import os
import sys
import json
import time
import random
import datetime
import sqlite3
import hashlib
import mimetypes
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Any, Union
from dataclasses import dataclass
from enum import Enum
from collections import defaultdict, Counter
import statistics
import math

try:
    from typing import TypeAlias
    JsonType: TypeAlias = Dict[str, Any]
except ImportError:
    JsonType = Dict[str, Any]

# 数据处理
import base64
import io
import csv

# 图像处理
try:
    from PIL import Image, ImageDraw, ImageFont, ImageFilter
    HAS_PILLOW = True
except ImportError:
    HAS_PILLOW = False
    print("警告: Pillow库未安装，图片功能将受限")

# Web框架 - 使用内置http.server或简单的HTML界面
from http.server import HTTPServer, BaseHTTPRequestHandler
import socketserver
import threading

# ================ 数据类定义 ================
class GarbageCategory(Enum):
    """垃圾分类枚举"""
    RECYCLABLE = "可回收物"
    HAZARDOUS = "有害垃圾"
    KITCHEN = "厨余垃圾"
    OTHER = "其他垃圾"

@dataclass
class GarbageItem:
    """垃圾物品数据类"""
    name: str
    category: GarbageCategory
    description: str
    disposal_method: str
    tips: str
    keywords: List[str]

@dataclass
class RecognitionResult:
    """识别结果数据类"""
    item: GarbageItem
    confidence: float
    timestamp: datetime.datetime
    image_hash: Optional[str] = None

@dataclass
class UserRecord:
    """用户记录数据类"""
    user_id: str
    action: str
    item_name: str
    category: str
    timestamp: datetime.datetime
    confidence: Optional[float] = None

# ================ 配置管理器 ================
class ConfigManager:
    """配置管理器"""
    
    # 使用Python 3.13的类属性语法
    _instance: Optional['ConfigManager'] = None
    
    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._initialize()
        return cls._instance
    
    def _initialize(self):
        """初始化配置"""
        self.base_dir = Path(__file__).parent
        self.data_dir = self.base_dir / "data"
        self.images_dir = self.data_dir / "images"
        self.db_path = self.data_dir / "garbage.db"
        
        # 创建目录
        self.data_dir.mkdir(exist_ok=True)
        self.images_dir.mkdir(exist_ok=True)
        
        # 颜色配置 - 使用RGB元组
        self.colors = {
            GarbageCategory.RECYCLABLE: (30, 144, 255),   # 蓝色
            GarbageCategory.HAZARDOUS: (255, 69, 0),      # 红色
            GarbageCategory.KITCHEN: (50, 205, 50),       # 绿色
            GarbageCategory.OTHER: (169, 169, 169)        # 灰色
        }
        
        # 模型配置
        self.model_config = {
            "rules_weight": 0.7,
            "keyword_weight": 0.3,
            "min_confidence": 0.5,
            "similarity_threshold": 0.8
        }
        
        # 界面配置
        self.ui_config = {
            "port": 8080,
            "host": "localhost",
            "max_image_size": 5 * 1024 * 1024,  # 5MB
            "supported_formats": {".jpg", ".jpeg", ".png", ".gif"}
        }
    
    def get_color_hex(self, category: GarbageCategory) -> str:
        """获取颜色的十六进制表示"""
        r, g, b = self.colors[category]
        return f"#{r:02x}{g:02x}{b:02x}"
    
    def get_color_rgb(self, category: GarbageCategory) -> Tuple[int, int, int]:
        """获取RGB颜色"""
        return self.colors[category]

# ================ 垃圾分类知识库 ================
class GarbageKnowledgeBase:
    """垃圾分类知识库"""
    
    def __init__(self):
        self.config = ConfigManager()
        self.items: List[GarbageItem] = []
        self.keyword_index: Dict[str, List[GarbageItem]] = defaultdict(list)
        self._load_default_data()
        self._build_index()
    
    def _load_default_data(self):
        """加载默认数据"""
        # 使用Python 3.13+的match语句（结构模式匹配）
        default_items = [
            # 可回收物
            GarbageItem(
                name="塑料瓶",
                category=GarbageCategory.RECYCLABLE,
                description="塑料制品，常见于饮料包装",
                disposal_method="清洗干净，压扁后投放",
                tips="瓶盖通常属于其他垃圾",
                keywords=["塑料", "瓶子", "饮料瓶", "矿泉水瓶"]
            ),
            GarbageItem(
                name="易拉罐",
                category=GarbageCategory.RECYCLABLE,
                description="金属制品，常见于饮料包装",
                disposal_method="压扁后投放",
                tips="保持干燥清洁",
                keywords=["易拉罐", "铝罐", "金属", "罐头"]
            ),
            GarbageItem(
                name="报纸",
                category=GarbageCategory.RECYCLABLE,
                description="纸制品，可回收利用",
                disposal_method="叠放整齐后投放",
                tips="受污染的纸不属于可回收物",
                keywords=["报纸", "纸张", "纸制品", "废纸"]
            ),
            GarbageItem(
                name="玻璃瓶",
                category=GarbageCategory.RECYCLABLE,
                description="玻璃制品，可回收利用",
                disposal_method="轻放避免破碎",
                tips="有破损的玻璃要小心处理",
                keywords=["玻璃", "瓶子", "玻璃瓶", "酒瓶"]
            ),
            
            # 有害垃圾
            GarbageItem(
                name="电池",
                category=GarbageCategory.HAZARDOUS,
                description="含重金属，对环境有害",
                disposal_method="投放至有害垃圾桶",
                tips="不要随意丢弃",
                keywords=["电池", "干电池", "充电电池", "锂电池"]
            ),
            GarbageItem(
                name="过期药品",
                category=GarbageCategory.HAZARDOUS,
                description="化学物质，可能污染环境",
                disposal_method="投放至有害垃圾桶",
                tips="最好保持原包装",
                keywords=["药品", "过期药", "西药", "中药"]
            ),
            GarbageItem(
                name="灯管",
                category=GarbageCategory.HAZARDOUS,
                description="含汞，有害物质",
                disposal_method="轻放避免破碎",
                tips="节能灯也属于此类",
                keywords=["灯管", "日光灯", "节能灯", "灯泡"]
            ),
            GarbageItem(
                name="油漆桶",
                category=GarbageCategory.HAZARDOUS,
                description="化学物质，有害环境",
                disposal_method="密封后投放",
                tips="残留油漆要倒出",
                keywords=["油漆", "涂料", "油漆桶", "颜料"]
            ),
            
            # 厨余垃圾
            GarbageItem(
                name="剩饭剩菜",
                category=GarbageCategory.KITCHEN,
                description="食物残渣，易腐烂",
                disposal_method="沥干水分后投放",
                tips="尽量去除包装",
                keywords=["剩饭", "剩菜", "饭菜", "食物残渣"]
            ),
            GarbageItem(
                name="果皮",
                category=GarbageCategory.KITCHEN,
                description="水果残余，有机质",
                disposal_method="直接投放",
                tips="柚子皮等较硬的可作为其他垃圾",
                keywords=["果皮", "水果皮", "香蕉皮", "苹果核"]
            ),
            GarbageItem(
                name="茶叶渣",
                category=GarbageCategory.KITCHEN,
                description="植物残余，有机质",
                disposal_method="沥干水分后投放",
                tips="茶包要分开处理",
                keywords=["茶叶", "茶渣", "茶包", "茶叶渣"]
            ),
            GarbageItem(
                name="蛋壳",
                category=GarbageCategory.KITCHEN,
                description="食物残余，有机质",
                disposal_method="直接投放",
                tips="保持干燥",
                keywords=["蛋壳", "鸡蛋壳", "鸭蛋壳"]
            ),
            
            # 其他垃圾
            GarbageItem(
                name="卫生纸",
                category=GarbageCategory.OTHER,
                description="受污染纸张，不可回收",
                disposal_method="直接投放",
                tips="遇水即溶的纸张",
                keywords=["卫生纸", "纸巾", "厕纸", "面巾纸"]
            ),
            GarbageItem(
                name="陶瓷碎片",
                category=GarbageCategory.OTHER,
                description="不可回收材料",
                disposal_method="包裹后投放",
                tips="小心划伤",
                keywords=["陶瓷", "瓷器", "碎片", "碗碟"]
            ),
            GarbageItem(
                name="烟头",
                category=GarbageCategory.OTHER,
                description="烟草残余，有害物质",
                disposal_method="确保熄灭后投放",
                tips="含有害物质",
                keywords=["烟头", "香烟", "烟蒂", "烟灰"]
            ),
            GarbageItem(
                name="塑料袋",
                category=GarbageCategory.OTHER,
                description="受污染塑料，不可回收",
                disposal_method="直接投放",
                tips="干净的可作为可回收物",
                keywords=["塑料袋", "塑料膜", "包装袋"]
            ),
        ]
        
        self.items = default_items
    
    def _build_index(self):
        """构建关键词索引"""
        for item in self.items:
            for keyword in item.keywords:
                self.keyword_index[keyword].append(item)
    
    def search_by_name(self, name: str) -> Optional[GarbageItem]:
        """通过名称搜索"""
        name_lower = name.lower()
        for item in self.items:
            if name_lower in item.name.lower() or item.name.lower() in name_lower:
                return item
        return None
    
    def search_by_keyword(self, keyword: str) -> List[GarbageItem]:
        """通过关键词搜索"""
        keyword_lower = keyword.lower()
        results = []
        
        # 直接匹配
        if keyword_lower in self.keyword_index:
            results.extend(self.keyword_index[keyword_lower])
        
        # 模糊匹配
        for kw, items in self.keyword_index.items():
            if keyword_lower in kw or kw in keyword_lower:
                for item in items:
                    if item not in results:
                        results.append(item)
        
        return results
    
    def classify_by_text(self, text: str) -> List[Tuple[GarbageItem, float]]:
        """通过文本分类"""
        text_lower = text.lower()
        results = []
        
        # 检查完全匹配
        for item in self.items:
            if item.name.lower() == text_lower:
                results.append((item, 1.0))
                return results
        
        # 关键词匹配
        matched_items = {}
        for item in self.items:
            # 计算匹配分数
            score = 0.0
            
            # 名称部分匹配
            if text_lower in item.name.lower():
                score += 0.4
            
            # 关键词匹配
            keyword_matches = sum(1 for kw in item.keywords if kw in text_lower)
            if keyword_matches > 0:
                score += 0.3 * (keyword_matches / len(item.keywords))
            
            # 描述匹配
            if text_lower in item.description.lower():
                score += 0.2
            
            if score > 0:
                matched_items[item] = score
        
        # 排序并返回
        sorted_results = sorted(matched_items.items(), key=lambda x: x[1], reverse=True)
        return sorted_results[:5]  # 返回前5个结果
    
    def get_examples_by_category(self, category: GarbageCategory) -> List[str]:
        """获取分类的示例"""
        examples = []
        for item in self.items:
            if item.category == category:
                examples.append(item.name)
        return examples[:5]  # 返回最多5个示例

# ================ 规则引擎 ================
class RuleEngine:
    """垃圾分类规则引擎"""
    
    def __init__(self, knowledge_base: GarbageKnowledgeBase):
        self.kb = knowledge_base
        self.config = ConfigManager()
        
        # 定义规则
        self.rules = self._define_rules()
    
    def _define_rules(self) -> Dict[str, Any]:
        """定义分类规则"""
        return {
            "material_rules": {
                "塑料": {"weight": 0.3, "categories": [GarbageCategory.RECYCLABLE, GarbageCategory.OTHER]},
                "金属": {"weight": 0.4, "category": GarbageCategory.RECYCLABLE},
                "纸张": {"weight": 0.3, "categories": [GarbageCategory.RECYCLABLE, GarbageCategory.OTHER]},
                "玻璃": {"weight": 0.4, "category": GarbageCategory.RECYCLABLE},
                "食物": {"weight": 0.5, "category": GarbageCategory.KITCHEN},
                "化学": {"weight": 0.6, "category": GarbageCategory.HAZARDOUS},
                "纺织品": {"weight": 0.2, "category": GarbageCategory.OTHER},
            },
            "usage_rules": {
                "包装": {"weight": 0.3, "categories": [GarbageCategory.RECYCLABLE, GarbageCategory.OTHER]},
                "容器": {"weight": 0.4, "categories": [GarbageCategory.RECYCLABLE, GarbageCategory.OTHER]},
                "电器": {"weight": 0.5, "category": GarbageCategory.HAZARDOUS},
                "餐具": {"weight": 0.3, "category": GarbageCategory.OTHER},
                "卫生": {"weight": 0.4, "category": GarbageCategory.OTHER},
            },
            "state_rules": {
                "潮湿": {"weight": 0.5, "category": GarbageCategory.OTHER},
                "干燥": {"weight": 0.2, "effect": "可回收性增加"},
                "破碎": {"weight": 0.6, "effect": "可能变为其他垃圾"},
                "污染": {"weight": 0.7, "category": GarbageCategory.OTHER},
                "清洁": {"weight": 0.1, "effect": "可回收性增加"},
            }
        }
    
    def apply_rules(self, text_description: str) -> Dict[GarbageCategory, float]:
        """应用规则到文本描述"""
        text_lower = text_description.lower()
        scores = defaultdict(float)
        
        # 材料规则
        for material, rule in self.rules["material_rules"].items():
            if material in text_lower:
                if "category" in rule:
                    scores[rule["category"]] += rule["weight"]
                elif "categories" in rule:
                    for category in rule["categories"]:
                        scores[category] += rule["weight"] / len(rule["categories"])
        
        # 用途规则
        for usage, rule in self.rules["usage_rules"].items():
            if usage in text_lower:
                if "category" in rule:
                    scores[rule["category"]] += rule["weight"]
                elif "categories" in rule:
                    for category in rule["categories"]:
                        scores[category] += rule["weight"] / len(rule["categories"])
        
        # 状态规则（调整分数）
        for state, rule in self.rules["state_rules"].items():
            if state in text_lower:
                if "category" in rule:
                    scores[rule["category"]] += rule["weight"]
                elif "effect" in rule:
                    # 调整其他类别的分数
                    if "增加" in rule["effect"]:
                        for category in scores:
                            if category == GarbageCategory.RECYCLABLE:
                                scores[category] += 0.1
                    elif "减少" in rule["effect"] or "变为" in rule["effect"]:
                        for category in scores:
                            if category != GarbageCategory.OTHER:
                                scores[category] *= 0.8
                                scores[GarbageCategory.OTHER] += 0.2
        
        # 归一化分数
        total = sum(scores.values())
        if total > 0:
            for category in scores:
                scores[category] /= total
        
        return dict(scores)
    
    def combine_with_keyword_search(self, text: str) -> List[Tuple[GarbageCategory, float]]:
        """结合规则和关键词搜索"""
        # 获取规则分数
        rule_scores = self.apply_rules(text)
        
        # 获取关键词搜索结果
        keyword_results = self.kb.classify_by_text(text)
        
        # 合并分数
        combined_scores = defaultdict(float)
        
        # 添加规则分数
        for category, score in rule_scores.items():
            combined_scores[category] += score * self.config.model_config["rules_weight"]
        
        # 添加关键词匹配分数
        for item, confidence in keyword_results:
            combined_scores[item.category] += confidence * self.config.model_config["keyword_weight"]
        
        # 排序并返回
        sorted_results = sorted(combined_scores.items(), key=lambda x: x[1], reverse=True)
        return sorted_results

# ================ 简单图像分析器 ================
class SimpleImageAnalyzer:
    """简单图像分析器（不使用深度学习）"""
    
    def __init__(self):
        self.config = ConfigManager()
        self.colors = self.config.colors
    
    def analyze_image(self, image_path: Union[str, Path]) -> Dict[str, Any]:
        """分析图像特征"""
        if not HAS_PILLOW:
            return {"error": "Pillow库未安装，无法分析图片"}
        
        try:
            with Image.open(image_path) as img:
                # 转换为RGB模式
                if img.mode != 'RGB':
                    img = img.convert('RGB')
                
                # 获取基本信息
                width, height = img.size
                aspect_ratio = width / height
                
                # 分析颜色
                color_info = self._analyze_colors(img)
                
                # 分析纹理/边缘（简单版本）
                texture_info = self._analyze_texture(img)
                
                # 生成图像哈希
                img_hash = self._generate_image_hash(img)
                
                return {
                    "dimensions": {"width": width, "height": height},
                    "aspect_ratio": aspect_ratio,
                    "color_dominant": color_info["dominant"],
                    "color_palette": color_info["palette"],
                    "brightness": color_info["brightness"],
                    "contrast": texture_info["contrast"],
                    "edges": texture_info["edges"],
                    "hash": img_hash,
                    "format": img.format
                }
        
        except Exception as e:
            return {"error": f"图像分析失败: {str(e)}"}
    
    def _analyze_colors(self, img: Image.Image) -> Dict[str, Any]:
        """分析颜色特征"""
        # 缩小图片以加快处理
        img_small = img.resize((100, 100))
        pixels = list(img_small.getdata())
        
        # 计算平均颜色
        total_r = total_g = total_b = 0
        for r, g, b in pixels:
            total_r += r
            total_g += g
            total_b += b
        
        avg_r = total_r // len(pixels)
        avg_g = total_g // len(pixels)
        avg_b = total_b // len(pixels)
        
        # 计算亮度
        brightness = (0.299 * avg_r + 0.587 * avg_g + 0.114 * avg_b) / 255
        
        # 找出主要颜色（简化版）
        color_counts = Counter(pixels)
        dominant_colors = color_counts.most_common(5)
        
        return {
            "dominant": (avg_r, avg_g, avg_b),
            "palette": dominant_colors,
            "brightness": brightness
        }
    
    def _analyze_texture(self, img: Image.Image) -> Dict[str, float]:
        """分析纹理特征"""
        # 转换为灰度图
        gray_img = img.convert('L')
        pixels = list(gray_img.getdata())
        
        # 计算对比度（标准差）
        if len(pixels) > 1:
            contrast = statistics.stdev(pixels) / 255
        else:
            contrast = 0.0
        
        # 简单边缘检测（水平差异）
        width, height = gray_img.size
        edge_score = 0.0
        
        for y in range(height - 1):
            for x in range(width - 1):
                # 计算水平差异
                diff_h = abs(pixels[y * width + x] - pixels[y * width + x + 1])
                # 计算垂直差异
                diff_v = abs(pixels[y * width + x] - pixels[(y + 1) * width + x])
                edge_score += (diff_h + diff_v)
        
        # 归一化
        if width > 0 and height > 0:
            edge_score = edge_score / (width * height * 510)  # 510 = 255*2
        
        return {
            "contrast": contrast,
            "edges": edge_score
        }
    
    def _generate_image_hash(self, img: Image.Image) -> str:
        """生成图像哈希"""
        # 缩小图片
        img_small = img.resize((8, 8)).convert('L')
        
        # 计算平均值
        pixels = list(img_small.getdata())
        avg = sum(pixels) / len(pixels)
        
        # 生成哈希位
        bits = []
        for pixel in pixels:
            bits.append('1' if pixel > avg else '0')
        
        # 转换为十六进制
        hash_hex = ''
        for i in range(0, 64, 4):
            nibble = bits[i:i+4]
            hash_hex += hex(int(''.join(nibble), 2))[2:]
        
        return hash_hex
    
    def predict_from_image(self, image_path: Union[str, Path], 
                          text_hint: Optional[str] = None) -> List[Tuple[GarbageCategory, float]]:
        """从图像预测分类"""
        # 分析图像
        analysis = self.analyze_image(image_path)
        
        if "error" in analysis:
            # 如果图像分析失败，回退到文本分析
            if text_hint:
                return [(GarbageCategory.OTHER, 0.5)]
            else:
                return [(GarbageCategory.OTHER, 0.3)]
        
        # 基于颜色和纹理的简单规则
        scores = defaultdict(float)
        
        # 颜色规则
        brightness = analysis["brightness"]
        contrast = analysis["contrast"]
        
        # 明亮、高对比度的可能是塑料/金属（可回收）
        if brightness > 0.6 and contrast > 0.3:
            scores[GarbageCategory.RECYCLABLE] += 0.4
        
        # 暗淡、低对比度的可能是厨余
        if brightness < 0.4 and contrast < 0.2:
            scores[GarbageCategory.KITCHEN] += 0.3
        
        # 红色调的可能是有害垃圾
        dominant_r = analysis["color_dominant"][0]
        if dominant_r > 150 and brightness < 0.5:
            scores[GarbageCategory.HAZARDOUS] += 0.3
        
        # 灰色调的可能是其他垃圾
        if 0.3 <= brightness <= 0.7 and contrast < 0.25:
            scores[GarbageCategory.OTHER] += 0.3
        
        # 如果有文本提示，结合提示
        if text_hint:
            # 简单的文本匹配
            text_lower = text_hint.lower()
            if any(kw in text_lower for kw in ["塑料", "金属", "玻璃"]):
                scores[GarbageCategory.RECYCLABLE] += 0.2
            elif any(kw in text_lower for kw in ["电池", "药品", "油漆"]):
                scores[GarbageCategory.HAZARDOUS] += 0.2
            elif any(kw in text_lower for kw in ["食物", "果皮", "剩饭"]):
                scores[GarbageCategory.KITCHEN] += 0.2
        
        # 确保每个类别都有基础分数
        for category in GarbageCategory:
            if category not in scores:
                scores[category] = 0.1
        
        # 归一化
        total = sum(scores.values())
        if total > 0:
            for category in scores:
                scores[category] /= total
        
        # 排序返回
        return sorted(scores.items(), key=lambda x: x[1], reverse=True)

# ================ 数据库管理器 ================
class DatabaseManager:
    """数据库管理器"""
    
    def __init__(self, db_path: Union[str, Path]):
        self.db_path = Path(db_path)
        self.conn = None
        self._initialize_database()
    
    def _initialize_database(self):
        """初始化数据库"""
        self.conn = sqlite3.connect(self.db_path)
        cursor = self.conn.cursor()
        
        # 创建用户记录表
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS user_records (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id TEXT NOT NULL,
                action TEXT NOT NULL,
                item_name TEXT NOT NULL,
                category TEXT NOT NULL,
                confidence REAL,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        ''')
        
        # 创建图像记录表
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS image_records (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                image_hash TEXT UNIQUE,
                image_path TEXT,
                analysis_result TEXT,
                created_at DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        ''')
        
        # 创建统计表
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS statistics (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                date DATE NOT NULL,
                category TEXT NOT NULL,
                count INTEGER DEFAULT 0,
                UNIQUE(date, category)
            )
        ''')
        
        # 创建用户表
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                username TEXT UNIQUE NOT NULL,
                created_at DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        ''')
        
        self.conn.commit()
    
    def add_record(self, record: UserRecord) -> bool:
        """添加用户记录"""
        try:
            cursor = self.conn.cursor()
            cursor.execute('''
                INSERT INTO user_records 
                (user_id, action, item_name, category, confidence, timestamp)
                VALUES (?, ?, ?, ?, ?, ?)
            ''', (
                record.user_id,
                record.action,
                record.item_name,
                record.category,
                record.confidence,
                record.timestamp.isoformat()
            ))
            
            # 更新统计
            today = datetime.date.today()
            cursor.execute('''
                INSERT OR IGNORE INTO statistics (date, category, count)
                VALUES (?, ?, 0)
            ''', (today.isoformat(), record.category))
            
            cursor.execute('''
                UPDATE statistics 
                SET count = count + 1 
                WHERE date = ? AND category = ?
            ''', (today.isoformat(), record.category))
            
            self.conn.commit()
            return True
            
        except Exception as e:
            print(f"添加记录失败: {e}")
            return False
    
    def add_image_record(self, image_hash: str, image_path: str, 
                        analysis_result: Dict[str, Any]) -> bool:
        """添加图像记录"""
        try:
            cursor = self.conn.cursor()
            cursor.execute('''
                INSERT OR REPLACE INTO image_records 
                (image_hash, image_path, analysis_result)
                VALUES (?, ?, ?)
            ''', (
                image_hash,
                str(image_path),
                json.dumps(analysis_result)
            ))
            self.conn.commit()
            return True
        except Exception as e:
            print(f"添加图像记录失败: {e}")
            return False
    
    def get_user_records(self, user_id: str, limit: int = 50) -> List[Dict[str, Any]]:
        """获取用户记录"""
        cursor = self.conn.cursor()
        cursor.execute('''
            SELECT item_name, category, confidence, timestamp
            FROM user_records
            WHERE user_id = ?
            ORDER BY timestamp DESC
            LIMIT ?
        ''', (user_id, limit))
        
        records = []
        for row in cursor.fetchall():
            records.append({
                "item_name": row[0],
                "category": row[1],
                "confidence": row[2],
                "timestamp": row[3]
            })
        
        return records
    
    def get_statistics(self, days: int = 7) -> Dict[str, Any]:
        """获取统计信息"""
        cursor = self.conn.cursor()
        
        # 获取分类统计
        cursor.execute('''
            SELECT category, SUM(count) as total
            FROM statistics
            WHERE date >= date('now', ?)
            GROUP BY category
        ''', (f'-{days} days',))
        
        category_stats = {}
        for row in cursor.fetchall():
            category_stats[row[0]] = row[1]
        
        # 获取用户活跃度
        cursor.execute('''
            SELECT user_id, COUNT(*) as count
            FROM user_records
            WHERE timestamp >= datetime('now', ?)
            GROUP BY user_id
            ORDER BY count DESC
            LIMIT 10
        ''', (f'-{days} days',))
        
        user_activity = []
        for row in cursor.fetchall():
            user_activity.append({
                "user_id": row[0],
                "count": row[1]
            })
        
        return {
            "category_stats": category_stats,
            "user_activity": user_activity,
            "total_days": days
        }
    
    def close(self):
        """关闭数据库连接"""
        if self.conn:
            self.conn.close()

# ================ Web界面 ================
class GarbageClassificationUI:
    """垃圾分类Web界面"""
    
    def __init__(self, port: int = 8080):
        self.port = port
        self.config = ConfigManager()
        self.knowledge_base = GarbageKnowledgeBase()
        self.rule_engine = RuleEngine(self.knowledge_base)
        self.image_analyzer = SimpleImageAnalyzer()
        self.db = DatabaseManager(self.config.db_path)
        self.current_user = "guest"
        
        # HTML模板
        self.html_templates = self._load_templates()
    
    def _load_templates(self) -> Dict[str, str]:
        """加载HTML模板"""
        return {
            "base": '''<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{title}</title>
    <style>
        * {{
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }}
        
        body {{
            font-family: 'Microsoft YaHei', Arial, sans-serif;
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            min-height: 100vh;
            padding: 20px;
        }}
        
        .container {{
            max-width: 1200px;
            margin: 0 auto;
        }}
        
        .header {{
            text-align: center;
            margin-bottom: 30px;
            color: white;
        }}
        
        .header h1 {{
            font-size: 2.5em;
            margin-bottom: 10px;
            text-shadow: 2px 2px 4px rgba(0,0,0,0.3);
        }}
        
        .header p {{
            font-size: 1.2em;
            opacity: 0.9;
        }}
        
        .card {{
            background: white;
            border-radius: 15px;
            padding: 25px;
            margin-bottom: 25px;
            box-shadow: 0 10px 30px rgba(0,0,0,0.2);
        }}
        
        .card h2 {{
            color: #333;
            margin-bottom: 20px;
            padding-bottom: 10px;
            border-bottom: 2px solid #f0f0f0;
        }}
        
        .category-badge {{
            display: inline-block;
            padding: 5px 15px;
            border-radius: 20px;
            color: white;
            font-weight: bold;
            margin: 5px;
            box-shadow: 0 2px 5px rgba(0,0,0,0.1);
        }}
        
        .btn {{
            display: inline-block;
            padding: 12px 25px;
            background: #4CAF50;
            color: white;
            border: none;
            border-radius: 25px;
            cursor: pointer;
            font-size: 1em;
            transition: all 0.3s;
            text-decoration: none;
            margin: 5px;
        }}
        
        .btn:hover {{
            background: #45a049;
            transform: translateY(-2px);
            box-shadow: 0 5px 15px rgba(0,0,0,0.2);
        }}
        
        .btn-secondary {{
            background: #2196F3;
        }}
        
        .btn-danger {{
            background: #f44336;
        }}
        
        .form-group {{
            margin-bottom: 20px;
        }}
        
        .form-group label {{
            display: block;
            margin-bottom: 8px;
            font-weight: bold;
            color: #555;
        }}
        
        .form-group input, .form-group textarea, .form-group select {{
            width: 100%;
            padding: 12px;
            border: 2px solid #ddd;
            border-radius: 8px;
            font-size: 1em;
            transition: border-color 0.3s;
        }}
        
        .form-group input:focus, .form-group textarea:focus, .form-group select:focus {{
            border-color: #4CAF50;
            outline: none;
        }}
        
        .result-box {{
            padding: 20px;
            border-radius: 10px;
            margin-top: 20px;
            border-left: 5px solid;
        }}
        
        .result-item {{
            padding: 15px;
            margin: 10px 0;
            background: #f9f9f9;
            border-radius: 8px;
            border-left: 4px solid;
        }}
        
        .stat-bar {{
            height: 30px;
            border-radius: 15px;
            margin: 10px 0;
            overflow: hidden;
            background: #eee;
        }}
        
        .stat-fill {{
            height: 100%;
            border-radius: 15px;
            text-align: center;
            line-height: 30px;
            color: white;
            font-weight: bold;
        }}
        
        .nav {{
            display: flex;
            justify-content: center;
            flex-wrap: wrap;
            margin-bottom: 30px;
            background: rgba(255,255,255,0.1);
            border-radius: 15px;
            padding: 15px;
        }}
        
        .nav a {{
            color: white;
            text-decoration: none;
            padding: 10px 20px;
            margin: 5px;
            border-radius: 25px;
            transition: all 0.3s;
        }}
        
        .nav a:hover, .nav a.active {{
            background: rgba(255,255,255,0.2);
        }}
        
        @media (max-width: 768px) {{
            .container {{
                padding: 10px;
            }}
            
            .card {{
                padding: 15px;
            }}
            
            .header h1 {{
                font-size: 2em;
            }}
        }}
    </style>
</head>
<body>
    <div class="container">
        <div class="header">
            <h1>♻️ 智能垃圾分类系统</h1>
            <p>Python 3.13.7 | 规则引擎 | 图像分析</p>
        </div>
        
        <div class="nav">
            {nav_links}
        </div>
        
        {content}
        
        <div class="card" style="text-align: center; margin-top: 30px;">
            <p>西北工业大学自动化学院 Python合作大作业 | Python 3.13.7 版本 | © 2025</p>
        </div>
    </div>
    
    <script>
        // 简单的JavaScript功能
        function showCategoryInfo(category) {{
            const info = {{
                '可回收物': '适宜回收利用的生活废弃物',
                '有害垃圾': '对人体健康或环境有害的生活废弃物',
                '厨余垃圾': '易腐烂的含有机质的生活废弃物',
                '其他垃圾': '除上述类别之外的其他生活废弃物'
            }};
            alert(category + ': ' + (info[category] || '暂无信息'));
        }}
        
        function copyToClipboard(text) {{
            navigator.clipboard.writeText(text).then(() => {{
                alert('已复制到剪贴板: ' + text);
            }});
        }}
        
        // 文件上传预览
        function previewImage(input) {{
            if (input.files && input.files[0]) {{
                const reader = new FileReader();
                reader.onload = function(e) {{
                    document.getElementById('imagePreview').innerHTML = 
                        '<img src="' + e.target.result + '" style="max-width:300px;border-radius:10px;">';
                }};
                reader.readAsDataURL(input.files[0]);
            }}
        }}
    </script>
</body>
</html>''',
            
            "home": '''<div class="card">
    <h2>🏠 系统介绍</h2>
    <p>欢迎使用智能垃圾分类系统！本系统采用规则引擎和图像分析技术，帮助您快速准确地进行垃圾分类。</p>
    
    <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(250px, 1fr)); gap: 20px; margin-top: 20px;">
        <div style="padding: 20px; background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); color: white; border-radius: 10px;">
            <h3>📸 图片识别</h3>
            <p>上传垃圾图片，系统通过图像分析智能分类</p>
        </div>
        
        <div style="padding: 20px; background: linear-gradient(135deg, #4CAF50 0%, #45a049 100%); color: white; border-radius: 10px;">
            <h3>🔍 文字查询</h3>
            <p>输入垃圾名称，获取详细分类信息和建议</p>
        </div>
        
        <div style="padding: 20px; background: linear-gradient(135deg, #2196F3 0%, #1976D2 100%); color: white; border-radius: 10px;">
            <h3>📊 数据统计</h3>
            <p>查看分类记录、统计图表和用户行为分析</p>
        </div>
        
        <div style="padding: 20px; background: linear-gradient(135deg, #f44336 0%, #d32f2f 100%); color: white; border-radius: 10px;">
            <h3>⚙️ 系统管理</h3>
            <p>管理知识库、查看系统状态和配置信息</p>
        </div>
    </div>
    
    <h3 style="margin-top: 30px;">垃圾分类标准</h3>
    <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 15px;">
        {category_cards}
    </div>
    
    <div style="text-align: center; margin-top: 30px;">
        <a href="/classify" class="btn">开始分类</a>
        <a href="/search" class="btn btn-secondary">文字查询</a>
        <a href="/stats" class="btn">查看统计</a>
    </div>
</div>

<div class="card">
    <h2>📝 最近记录</h2>
    {recent_records}
</div>''',
            
            "classify": '''<div class="card">
    <h2>📸 图片识别分类</h2>
    <p>上传垃圾图片，系统将通过图像分析技术识别垃圾类型</p>
    
    <form method="POST" action="/upload" enctype="multipart/form-data">
        <div class="form-group">
            <label for="image">选择图片文件 (JPG/PNG)</label>
            <input type="file" id="image" name="image" accept=".jpg,.jpeg,.png" required 
                   onchange="previewImage(this)">
            <div id="imagePreview" style="margin-top: 15px;"></div>
        </div>
        
        <div class="form-group">
            <label for="text_hint">文字提示（可选）</label>
            <input type="text" id="text_hint" name="text_hint" 
                   placeholder="如：塑料瓶、电池、剩饭等">
        </div>
        
        <div class="form-group">
            <label for="user_id">用户ID</label>
            <input type="text" id="user_id" name="user_id" value="{user_id}">
        </div>
        
        <button type="submit" class="btn">开始识别</button>
        <button type="reset" class="btn btn-secondary">重置</button>
    </form>
    
    {result_display}
</div>

<div class="card">
    <h2>💡 分类说明</h2>
    {category_explanations}
</div>''',
            
            "search": '''<div class="card">
    <h2>🔍 文字查询分类</h2>
    <p>输入垃圾名称或描述，系统将通过规则引擎进行智能分类</p>
    
    <form method="GET" action="/search_result">
        <div class="form-group">
            <label for="query">输入垃圾名称或描述</label>
            <input type="text" id="query" name="q" required 
                   placeholder="如：塑料瓶、电池、剩饭剩菜、卫生纸等" value="{query}">
        </div>
        
        <div class="form-group">
            <label for="user_id_search">用户ID</label>
            <input type="text" id="user_id_search" name="user_id" value="{user_id}">
        </div>
        
        <button type="submit" class="btn">查询</button>
        
        <div style="margin-top: 20px;">
            <p><strong>快速搜索：</strong></p>
            {quick_search_buttons}
        </div>
    </form>
    
    {search_results}
</div>''',
            
            "stats": '''<div class="card">
    <h2>📊 数据统计</h2>
    
    <form method="GET" action="/stats">
        <div style="display: flex; gap: 15px; margin-bottom: 20px;">
            <div class="form-group" style="flex: 1;">
                <label for="days">统计天数</label>
                <select id="days" name="days" onchange="this.form.submit()">
                    <option value="7" {selected_7}>最近7天</option>
                    <option value="30" {selected_30}>最近30天</option>
                    <option value="90" {selected_90}>最近90天</option>
                </select>
            </div>
            
            <div class="form-group" style="flex: 1;">
                <label for="user_filter">用户筛选</label>
                <select id="user_filter" name="user_filter" onchange="this.form.submit()">
                    <option value="all" {selected_all}>所有用户</option>
                    <option value="current" {selected_current}>当前用户</option>
                </select>
            </div>
        </div>
    </form>
    
    <h3>分类统计</h3>
    {category_stats}
    
    <h3 style="margin-top: 30px;">用户活跃度</h3>
    {user_activity}
    
    <h3 style="margin-top: 30px;">系统信息</h3>
    <div style="background: #f5f5f5; padding: 15px; border-radius: 8px;">
        <p><strong>Python版本：</strong> 3.13.7</p>
        <p><strong>知识库大小：</strong> {knowledge_base_size} 个物品</p>
        <p><strong>总记录数：</strong> {total_records} 条</p>
        <p><strong>系统状态：</strong> <span style="color: #4CAF50;">运行正常</span></p>
    </div>
</div>'''
        }
    
    def run_server(self):
        """运行Web服务器"""
        class RequestHandler(BaseHTTPRequestHandler):
            ui = self
            
            def do_GET(self):
                """处理GET请求"""
                try:
                    if self.path == '/':
                        self._send_home_page()
                    elif self.path == '/classify':
                        self._send_classify_page()
                    elif self.path == '/search':
                        self._send_search_page()
                    elif self.path.startswith('/search_result'):
                        self._handle_search_result()
                    elif self.path == '/stats':
                        self._send_stats_page()
                    elif self.path == '/favicon.ico':
                        self.send_error(404)
                    else:
                        self._send_home_page()
                
                except Exception as e:
                    self.send_error(500, f"服务器错误: {str(e)}")
            
            def do_POST(self):
                """处理POST请求"""
                if self.path == '/upload':
                    self._handle_upload()
                else:
                    self.send_error(404)
            
            def _send_home_page(self):
                """发送首页"""
                # 生成分类卡片
                category_cards = []
                for category in GarbageCategory:
                    examples = self.ui.knowledge_base.get_examples_by_category(category)
                    color = self.ui.config.get_color_hex(category)
                    
                    category_html = f'''
                    <div style="border-left: 5px solid {color}; padding: 15px; background: #f9f9f9; border-radius: 5px;">
                        <h4 style="color: {color}; margin-bottom: 10px;">{category.value}</h4>
                        <p style="font-size: 0.9em; color: #666;">{', '.join(examples[:3])}</p>
                    </div>
                    '''
                    category_cards.append(category_html)
                
                # 获取最近记录
                recent_records = self.ui.db.get_user_records("guest", 5)
                records_html = ""
                if recent_records:
                    for record in recent_records:
                        category_color = ""
                        for cat in GarbageCategory:
                            if cat.value == record["category"]:
                                category_color = self.ui.config.get_color_hex(cat)
                                break
                        
                        records_html += f'''
                        <div class="result-item" style="border-left-color: {category_color};">
                            <strong>{record['item_name']}</strong> → 
                            <span style="color: {category_color}; font-weight: bold;">{record['category']}</span>
                            <small style="float: right; color: #888;">{record['timestamp'][:16]}</small>
                        </div>
                        '''
                else:
                    records_html = "<p>暂无记录</p>"
                
                # 生成导航链接
                nav_links = '''
                <a href="/" class="active">🏠 首页</a>
                <a href="/classify">📸 图片识别</a>
                <a href="/search">🔍 文字查询</a>
                <a href="/stats">📊 数据统计</a>
                '''
                
                content = self.ui.html_templates["home"].format(
                    category_cards="\n".join(category_cards),
                    recent_records=records_html
                )
                
                html = self.ui.html_templates["base"].format(
                    title="智能垃圾分类系统 - 首页",
                    nav_links=nav_links,
                    content=content
                )
                
                self._send_html_response(html)
            
            def _send_classify_page(self):
                """发送图片识别页面"""
                # 生成分类说明
                explanations = []
                for category in GarbageCategory:
                    color = self.ui.config.get_color_hex(category)
                    items = self.ui.knowledge_base.get_examples_by_category(category)
                    
                    explanation = f'''
                    <div style="margin-bottom: 15px; padding: 10px; border-left: 3px solid {color};">
                        <strong style="color: {color};">{category.value}:</strong>
                        <span style="color: #666;"> {', '.join(items[:3])}等</span>
                    </div>
                    '''
                    explanations.append(explanation)
                
                # 生成导航链接
                nav_links = '''
                <a href="/">🏠 首页</a>
                <a href="/classify" class="active">📸 图片识别</a>
                <a href="/search">🔍 文字查询</a>
                <a href="/stats">📊 数据统计</a>
                '''
                
                content = self.ui.html_templates["classify"].format(
                    user_id=self.ui.current_user,
                    result_display="",
                    category_explanations="\n".join(explanations)
                )
                
                html = self.ui.html_templates["base"].format(
                    title="智能垃圾分类系统 - 图片识别",
                    nav_links=nav_links,
                    content=content
                )
                
                self._send_html_response(html)
            
            def _send_search_page(self):
                """发送搜索页面"""
                # 生成快速搜索按钮
                quick_search_items = ["塑料瓶", "电池", "剩饭", "卫生纸", "玻璃瓶", "果皮"]
                quick_buttons = []
                
                for item in quick_search_items:
                    quick_buttons.append(f'''
                    <a href="/search_result?q={item}&user_id={self.ui.current_user}" 
                       class="btn" style="padding: 8px 15px; font-size: 0.9em;">{item}</a>
                    ''')
                
                # 生成导航链接
                nav_links = '''
                <a href="/">🏠 首页</a>
                <a href="/classify">📸 图片识别</a>
                <a href="/search" class="active">🔍 文字查询</a>
                <a href="/stats">📊 数据统计</a>
                '''
                
                content = self.ui.html_templates["search"].format(
                    query="",
                    user_id=self.ui.current_user,
                    quick_search_buttons="\n".join(quick_buttons),
                    search_results=""
                )
                
                html = self.ui.html_templates["base"].format(
                    title="智能垃圾分类系统 - 文字查询",
                    nav_links=nav_links,
                    content=content
                )
                
                self._send_html_response(html)
            
            def _handle_search_result(self):
                """处理搜索结果"""
                from urllib.parse import parse_qs, urlparse
                
                # 解析查询参数
                parsed = urlparse(self.path)
                query_params = parse_qs(parsed.query)
                
                query = query_params.get('q', [''])[0]
                user_id = query_params.get('user_id', [self.ui.current_user])[0]
                
                if not query:
                    self._send_search_page()
                    return
                
                # 执行搜索
                results = self.ui.rule_engine.combine_with_keyword_search(query)
                
                # 生成结果HTML
                results_html = "<h3>🔎 搜索结果</h3>"
                
                if results:
                    # 取最佳结果
                    best_category, best_score = results[0]
                    
                    # 保存记录
                    record = UserRecord(
                        user_id=user_id,
                        action="text_search",
                        item_name=query,
                        category=best_category.value,
                        timestamp=datetime.datetime.now(),
                        confidence=best_score
                    )
                    self.ui.db.add_record(record)
                    
                    # 显示最佳结果
                    results_html += f'''
                    <div class="result-box" style="border-left-color: {self.ui.config.get_color_hex(best_category)};">
                        <h4>最佳匹配：{query} → {best_category.value}</h4>
                        <p><strong>置信度：</strong> {best_score:.1%}</p>
                    </div>
                    '''
                    
                    # 显示所有结果
                    results_html += "<h4 style='margin-top: 20px;'>所有可能分类：</h4>"
                    for category, score in results[:5]:
                        color = self.ui.config.get_color_hex(category)
                        width = min(score * 100, 100)
                        
                        results_html += f'''
                        <div style="margin-bottom: 15px;">
                            <div style="display: flex; justify-content: space-between; margin-bottom: 5px;">
                                <span><span class="category-badge" style="background: {color};">{category.value}</span></span>
                                <span>{score:.1%}</span>
                            </div>
                            <div class="stat-bar">
                                <div class="stat-fill" style="width: {width}%; background: {color};">{width:.0f}%</div>
                            </div>
                        </div>
                        '''
                else:
                    results_html += "<p>未找到相关结果</p>"
                
                # 生成快速搜索按钮
                quick_search_items = ["塑料瓶", "电池", "剩饭", "卫生纸", "玻璃瓶", "果皮"]
                quick_buttons = []
                
                for item in quick_search_items:
                    quick_buttons.append(f'''
                    <a href="/search_result?q={item}&user_id={user_id}" 
                       class="btn" style="padding: 8px 15px; font-size: 0.9em;">{item}</a>
                    ''')
                
                # 生成导航链接
                nav_links = '''
                <a href="/">🏠 首页</a>
                <a href="/classify">📸 图片识别</a>
                <a href="/search" class="active">🔍 文字查询</a>
                <a href="/stats">📊 数据统计</a>
                '''
                
                content = self.ui.html_templates["search"].format(
                    query=query,
                    user_id=user_id,
                    quick_search_buttons="\n".join(quick_buttons),
                    search_results=results_html
                )
                
                html = self.ui.html_templates["base"].format(
                    title=f"搜索结果 - {query}",
                    nav_links=nav_links,
                    content=content
                )
                
                self._send_html_response(html)
            
            def _send_stats_page(self):
                """发送统计页面"""
                from urllib.parse import parse_qs, urlparse
                
                # 解析查询参数
                parsed = urlparse(self.path)
                query_params = parse_qs(parsed.query)
                
                days = int(query_params.get('days', ['7'])[0])
                user_filter = query_params.get('user_filter', ['all'])[0]
                
                # 获取统计信息
                stats = self.ui.db.get_statistics(days)
                
                # 生成分类统计HTML
                category_stats_html = ""
                total_items = sum(stats["category_stats"].values())
                
                for category_name, count in stats["category_stats"].items():
                    # 找到对应的枚举
                    category = None
                    for cat in GarbageCategory:
                        if cat.value == category_name:
                            category = cat
                            break
                    
                    if category:
                        color = self.ui.config.get_color_hex(category)
                        percentage = (count / total_items * 100) if total_items > 0 else 0
                        
                        category_stats_html += f'''
                        <div style="margin-bottom: 15px;">
                            <div style="display: flex; justify-content: space-between; margin-bottom: 5px;">
                                <span><span class="category-badge" style="background: {color};">{category_name}</span></span>
                                <span>{count} 次 ({percentage:.1f}%)</span>
                            </div>
                            <div class="stat-bar">
                                <div class="stat-fill" style="width: {percentage}%; background: {color};">{percentage:.0f}%</div>
                            </div>
                        </div>
                        '''
                
                if not category_stats_html:
                    category_stats_html = "<p>暂无统计数据</p>"
                
                # 生成用户活跃度HTML
                user_activity_html = ""
                if stats["user_activity"]:
                    for user in stats["user_activity"]:
                        user_activity_html += f'''
                        <div style="padding: 10px 15px; background: #f5f5f5; border-radius: 8px; margin-bottom: 10px;">
                            <strong>{user['user_id']}</strong>: {user['count']} 次查询
                        </div>
                        '''
                else:
                    user_activity_html = "<p>暂无用户活跃度数据</p>"
                
                # 生成选择器状态
                selected_7 = "selected" if days == 7 else ""
                selected_30 = "selected" if days == 30 else ""
                selected_90 = "selected" if days == 90 else ""
                selected_all = "selected" if user_filter == "all" else ""
                selected_current = "selected" if user_filter == "current" else ""
                
                # 生成导航链接
                nav_links = '''
                <a href="/">🏠 首页</a>
                <a href="/classify">📸 图片识别</a>
                <a href="/search">🔍 文字查询</a>
                <a href="/stats" class="active">📊 数据统计</a>
                '''
                
                content = self.ui.html_templates["stats"].format(
                    selected_7=selected_7,
                    selected_30=selected_30,
                    selected_90=selected_90,
                    selected_all=selected_all,
                    selected_current=selected_current,
                    category_stats=category_stats_html,
                    user_activity=user_activity_html,
                    knowledge_base_size=len(self.ui.knowledge_base.items),
                    total_records=total_items
                )
                
                html = self.ui.html_templates["base"].format(
                    title="智能垃圾分类系统 - 数据统计",
                    nav_links=nav_links,
                    content=content
                )
                
                self._send_html_response(html)
            
            def _handle_upload(self):
                """处理文件上传"""
                import cgi
                
                try:
                    # 解析表单数据
                    content_type, pdict = cgi.parse_header(self.headers['content-type'])
                    
                    if content_type != 'multipart/form-data':
                        self.send_error(400, "无效的内容类型")
                        return
                    
                    # 解析表单数据
                    form = cgi.FieldStorage(
                        fp=self.rfile,
                        headers=self.headers,
                        environ={
                            'REQUEST_METHOD': 'POST',
                            'CONTENT_TYPE': self.headers['Content-Type'],
                        }
                    )
                    
                    # 获取表单字段
                    image_file = form['image']
                    text_hint = form.getvalue('text_hint', '')
                    user_id = form.getvalue('user_id', self.ui.current_user)
                    
                    if not image_file.filename:
                        self.send_error(400, "未选择文件")
                        return
                    
                    # 保存上传的文件
                    upload_dir = self.ui.config.images_dir / "uploads"
                    upload_dir.mkdir(exist_ok=True)
                    
                    filename = f"{int(time.time())}_{image_file.filename}"
                    filepath = upload_dir / filename
                    
                    with open(filepath, 'wb') as f:
                        f.write(image_file.file.read())
                    
                    # 分析图像
                    predictions = self.ui.image_analyzer.predict_from_image(filepath, text_hint)
                    
                    # 获取最佳结果
                    if predictions:
                        best_category, best_score = predictions[0]
                        
                        # 保存记录
                        record = UserRecord(
                            user_id=user_id,
                            action="image_upload",
                            item_name=filename,
                            category=best_category.value,
                            timestamp=datetime.datetime.now(),
                            confidence=best_score
                        )
                        self.ui.db.add_record(record)
                        
                        # 生成结果HTML
                        results_html = f'''
                        <div class="result-box" style="border-left-color: {self.ui.config.get_color_hex(best_category)}; margin-top: 20px;">
                            <h3>🎯 识别结果</h3>
                            <p><strong>文件：</strong> {image_file.filename}</p>
                            <p><strong>最佳分类：</strong> 
                               <span class="category-badge" style="background: {self.ui.config.get_color_hex(best_category)};">
                                   {best_category.value}
                               </span>
                            </p>
                            <p><strong>置信度：</strong> {best_score:.1%}</p>
                            <p><strong>文字提示：</strong> {text_hint if text_hint else '无'}</p>
                            
                            <h4>所有可能分类：</h4>
                        '''
                        
                        for category, score in predictions:
                            color = self.ui.config.get_color_hex(category)
                            width = min(score * 100, 100)
                            
                            results_html += f'''
                            <div style="margin-bottom: 10px;">
                                <div style="display: flex; justify-content: space-between; margin-bottom: 5px;">
                                    <span>{category.value}</span>
                                    <span>{score:.1%}</span>
                                </div>
                                <div class="stat-bar">
                                    <div class="stat-fill" style="width: {width}%; background: {color};">{width:.0f}%</div>
                                </div>
                            </div>
                            '''
                        
                        results_html += "</div>"
                    else:
                        results_html = "<div class='result-box'><p>识别失败</p></div>"
                    
                    # 生成分类说明
                    explanations = []
                    for category in GarbageCategory:
                        color = self.ui.config.get_color_hex(category)
                        items = self.ui.knowledge_base.get_examples_by_category(category)
                        
                        explanation = f'''
                        <div style="margin-bottom: 15px; padding: 10px; border-left: 3px solid {color};">
                            <strong style="color: {color};">{category.value}:</strong>
                            <span style="color: #666;"> {', '.join(items[:3])}等</span>
                        </div>
                        '''
                        explanations.append(explanation)
                    
                    # 生成导航链接
                    nav_links = '''
                    <a href="/">🏠 首页</a>
                    <a href="/classify" class="active">📸 图片识别</a>
                    <a href="/search">🔍 文字查询</a>
                    <a href="/stats">📊 数据统计</a>
                    '''
                    
                    content = self.ui.html_templates["classify"].format(
                        user_id=user_id,
                        result_display=results_html,
                        category_explanations="\n".join(explanations)
                    )
                    
                    html = self.ui.html_templates["base"].format(
                        title="智能垃圾分类系统 - 识别结果",
                        nav_links=nav_links,
                        content=content
                    )
                    
                    self._send_html_response(html)
                    
                except Exception as e:
                    self.send_error(500, f"上传处理失败: {str(e)}")
            
            def _send_html_response(self, html: str):
                """发送HTML响应"""
                self.send_response(200)
                self.send_header('Content-type', 'text/html; charset=utf-8')
                self.end_headers()
                self.wfile.write(html.encode('utf-8'))
            
            def log_message(self, format, *args):
                """重写日志方法"""
                # 可以在这里添加自定义日志逻辑
                pass
        
        # 启动服务器
        print(f"🚀 启动垃圾分类系统服务器...")
        print(f"📡 访问地址（请点击该链接跳转至网页）: http://{self.config.ui_config['host']}:{self.port}")
        print(f"🐍 Python版本: {sys.version}")
        print(f"📁 数据目录: {self.config.data_dir}")
        print(f"👤 默认用户: {self.current_user}")
        print("\n按 Ctrl+C 停止服务器\n")
        
        server = HTTPServer((self.config.ui_config['host'], self.port), RequestHandler)
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            print("\n🛑 服务器已停止")
            self.db.close()

# ================ 命令行界面 ================
class CommandLineInterface:
    """命令行界面"""
    
    def __init__(self):
        self.config = ConfigManager()
        self.knowledge_base = GarbageKnowledgeBase()
        self.rule_engine = RuleEngine(self.knowledge_base)
        self.image_analyzer = SimpleImageAnalyzer()
        self.db = DatabaseManager(self.config.db_path)
    
    def run(self):
        """运行命令行界面"""
        print("=" * 50)
        print("♻️  智能垃圾分类系统 - 命令行版本")
        print(f"🐍  Python {sys.version}")
        print("=" * 50)
        
        while True:
            print("\n请选择功能：")
            print("1. 文字查询分类")
            print("2. 查看分类示例")
            print("3. 查看统计数据")
            print("4. 测试图像分析")
            print("5. 查看最近记录")
            print("6. 退出系统")
            
            try:
                choice = input("\n请输入选项 (1-6): ").strip()
                
                if choice == '1':
                    self.text_classification()
                elif choice == '2':
                    self.show_examples()
                elif choice == '3':
                    self.show_statistics()
                elif choice == '4':
                    self.test_image_analysis()
                elif choice == '5':
                    self.show_recent_records()
                elif choice == '6':
                    print("👋 感谢使用，再见！")
                    break
                else:
                    print("❌ 无效选项，请重新输入")
            
            except KeyboardInterrupt:
                print("\n👋 感谢使用，再见！")
                break
            except Exception as e:
                print(f"❌ 发生错误: {e}")
    
    def text_classification(self):
        """文字分类"""
        print("\n" + "=" * 30)
        print("📝 文字查询分类")
        print("=" * 30)
        
        while True:
            query = input("\n请输入垃圾名称或描述 (输入 'q' 退出): ").strip()
            
            if query.lower() == 'q':
                break
            
            if not query:
                print("⚠️  输入不能为空")
                continue
            
            print(f"\n正在分析: {query}")
            
            # 执行分类
            results = self.rule_engine.combine_with_keyword_search(query)
            
            if results:
                print(f"\n✅ 分析完成！")
                
                # 显示最佳结果
                best_category, best_score = results[0]
                color = self.config.get_color_hex(best_category)
                
                print(f"\n🎯 最佳分类: {best_category.value} (置信度: {best_score:.1%})")
                
                # 显示所有结果
                print(f"\n📊 所有可能分类:")
                for i, (category, score) in enumerate(results[:5], 1):
                    print(f"  {i}. {category.value}: {score:.1%}")
                
                # 保存记录
                record = UserRecord(
                    user_id="cli_user",
                    action="text_classification",
                    item_name=query,
                    category=best_category.value,
                    timestamp=datetime.datetime.now(),
                    confidence=best_score
                )
                self.db.add_record(record)
                print(f"📝 记录已保存")
                
                # 显示处理建议
                item = self.knowledge_base.search_by_name(query)
                if item:
                    print(f"\n💡 处理建议: {item.disposal_method}")
                    print(f"📌 小贴士: {item.tips}")
            else:
                print("❌ 未找到相关分类")
    
    def show_examples(self):
        """显示分类示例"""
        print("\n" + "=" * 30)
        print("📋 垃圾分类示例")
        print("=" * 30)
        
        for category in GarbageCategory:
            color = self.config.get_color_hex(category)
            examples = self.knowledge_base.get_examples_by_category(category)
            
            print(f"\n{category.value}:")
            print(f"  示例: {', '.join(examples)}")
            print(f"  颜色: RGB{self.config.get_color_rgb(category)} ({color})")
    
    def show_statistics(self):
        """显示统计数据"""
        print("\n" + "=" * 30)
        print("📊 系统统计")
        print("=" * 30)
        
        stats = self.db.get_statistics(30)
        
        print(f"\n📅 最近30天统计:")
        
        if stats["category_stats"]:
            total = sum(stats["category_stats"].values())
            print(f"  总查询次数: {total}")
            
            for category_name, count in stats["category_stats"].items():
                percentage = (count / total * 100) if total > 0 else 0
                bar = "█" * int(percentage / 5)
                print(f"  {category_name}: {count}次 ({percentage:.1f}%) {bar}")
        else:
            print("  暂无统计数据")
        
        print(f"\n👥 用户活跃度:")
        if stats["user_activity"]:
            for user in stats["user_activity"]:
                print(f"  {user['user_id']}: {user['count']}次")
        else:
            print("  暂无用户活跃度数据")
        
        print(f"\n📚 知识库信息:")
        print(f"  总物品数: {len(self.knowledge_base.items)}")
        
        category_counts = Counter(item.category for item in self.knowledge_base.items)
        for category, count in category_counts.items():
            print(f"  {category.value}: {count}个")
    
    def test_image_analysis(self):
        """测试图像分析"""
        if not HAS_PILLOW:
            print("❌ Pillow库未安装，无法进行图像分析")
            return
        
        print("\n" + "=" * 30)
        print("🖼️  图像分析测试")
        print("=" * 30)
        
        # 创建测试图像
        test_dir = self.config.images_dir / "test"
        test_dir.mkdir(exist_ok=True)
        
        print("\n生成测试图像中...")
        
        # 为每个分类生成一个测试图像
        for category in GarbageCategory:
            color = self.config.get_color_rgb(category)
            
            # 创建图像
            img = Image.new('RGB', (300, 200), color=color)
            draw = ImageDraw.Draw(img)
            
            # 添加文字
            try:
                font = ImageFont.load_default()
                draw.text((100, 85), f"Test: {category.value}", fill=(255, 255, 255), font=font)
            except:
                pass
            
            # 保存图像
            filename = test_dir / f"test_{category.value}.png"
            img.save(filename)
            
            print(f"  已创建: {filename.name}")
        
        print("\n开始图像分析...")
        
        # 分析每个测试图像
        for category in GarbageCategory:
            filename = test_dir / f"test_{category.value}.png"
            
            print(f"\n分析 {category.value}:")
            
            # 分析图像
            predictions = self.image_analyzer.predict_from_image(filename)
            
            if predictions:
                for pred_category, score in predictions[:3]:
                    print(f"  {pred_category.value}: {score:.1%}")
            else:
                print("  分析失败")
    
    def show_recent_records(self):
        """显示最近记录"""
        print("\n" + "=" * 30)
        print("📝 最近记录")
        print("=" * 30)
        
        records = self.db.get_user_records("cli_user", 10)
        
        if records:
            for i, record in enumerate(records, 1):
                print(f"\n{i}. {record['item_name']}")
                print(f"   分类: {record['category']}")
                print(f"   置信度: {record['confidence']:.1% if record['confidence'] else 'N/A'}")
                print(f"   时间: {record['timestamp']}")
        else:
            print("暂无记录")

# ================ 主程序入口 ================
def main():
    """主函数"""
    print("智能垃圾分类系统 - Python 3.13.7 版本")
    print("=" * 50)
    
    # 检查Python版本
    required_version = (3, 13, 7)
    current_version = sys.version_info
    
    if current_version < required_version:
        print(f"⚠️  警告: 当前Python版本 {current_version.major}.{current_version.minor}.{current_version.micro}")
        print(f"   推荐使用 Python {required_version[0]}.{required_version[1]}.{required_version[2]} 或更高版本")
        print("   某些新特性可能无法使用")
    
    # 选择运行模式
    print("\n请选择运行模式:")
    print("1. Web界面模式 (推荐)")
    print("2. 命令行模式")
    print("3. 测试模式")
    
    try:
        choice = input("\n请输入选项 (1-3): ").strip()
        
        if choice == '1':
            # Web界面模式
            port = 8080
            try:
                port_input = input(f"请输入端口号 (默认: {port}): ").strip()
                if port_input:
                    port = int(port_input)
            except ValueError:
                print(f"⚠️  无效端口号，使用默认端口 {port}")
            
            ui = GarbageClassificationUI(port=port)
            ui.run_server()
        
        elif choice == '2':
            # 命令行模式
            cli = CommandLineInterface()
            cli.run()
        
        elif choice == '3':
            # 测试模式
            run_tests()
        
        else:
            print("❌ 无效选项")
    
    except KeyboardInterrupt:
        print("\n👋 程序已退出")
    except Exception as e:
        print(f"❌ 程序运行错误: {e}")
        import traceback
        traceback.print_exc()

def run_tests():
    """运行测试"""
    print("\n" + "=" * 50)
    print("🧪 系统测试")
    print("=" * 50)
    
    # 初始化组件
    config = ConfigManager()
    kb = GarbageKnowledgeBase()
    engine = RuleEngine(kb)
    
    print(f"✅ 配置管理器初始化完成")
    print(f"✅ 知识库加载完成: {len(kb.items)} 个物品")
    print(f"✅ 规则引擎初始化完成")
    
    # 测试搜索功能
    test_queries = ["塑料瓶", "电池", "剩饭", "未知物品"]
    
    print("\n🔍 测试搜索功能:")
    for query in test_queries:
        results = engine.combine_with_keyword_search(query)
        if results:
            best = results[0]
            print(f"  {query}: {best[0].value} ({best[1]:.1%})")
        else:
            print(f"  {query}: 未找到")
    
    # 测试数据库
    db = DatabaseManager(config.db_path)
    
    print("\n💾 测试数据库:")
    print(f"  数据库路径: {config.db_path}")
    print(f"  连接状态: {'正常' if db.conn else '异常'}")
    
    # 测试图像分析器（如果可用）
    if HAS_PILLOW:
        analyzer = SimpleImageAnalyzer()
        print("\n🖼️  测试图像分析器:")
        print(f"  Pillow版本: 可用")
        
        # 创建测试图像
        test_img = Image.new('RGB', (100, 100), color=(100, 150, 200))
        analysis = analyzer.analyze_image(test_img)
        
        if "error" not in analysis:
            print(f"  图像分析: 正常")
            print(f"  颜色分析: RGB{analysis['color_dominant']}")
        else:
            print(f"  图像分析: 失败 - {analysis['error']}")
    else:
        print("\n🖼️  测试图像分析器:")
        print(f"  Pillow: 未安装，跳过图像测试")
    
    db.close()
    print("\n✅ 测试完成!")

if __name__ == "__main__":
    main()