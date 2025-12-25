# 自定义 cgi.py，兼容旧脚本。因为笔者的电脑上没有cgi.
import urllib.parse
import os
import sys

def escape(s, quote=True):
    from html import escape
    return escape(s, quote=quote)

class FieldStorage:
    def __init__(self):
        self.params = {}
        # 解析 GET 参数
        query_string = os.environ.get("QUERY_STRING", "")
        get_params = urllib.parse.parse_qs(query_string)
        # 解析 POST 参数
        content_type = os.environ.get("CONTENT_TYPE", "")
        if "application/x-www-form-urlencoded" in content_type:
            content_length = int(os.environ.get("CONTENT_LENGTH", 0))
            post_data = sys.stdin.read(content_length)
            post_params = urllib.parse.parse_qs(post_data)
            # 合并 GET/POST 参数
            self.params = {**get_params, **post_params}
    
    def getvalue(self, key, default=None):
        values = self.params.get(key, [])
        return values[0] if values else default
    
    def getlist(self, key):
        return self.params.get(key, [])