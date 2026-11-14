"""只在明确开启且本机已配置真实服务时运行；不能用本地fixture代替。"""
import os
import unittest
from mathlib2_gateway.gateway import run_from_env
from mathlib2_gateway.__main__ import SMOKE_GOAL


@unittest.skipUnless(os.environ.get('MATHLIB2_GW_LIVE_TEST')=='1','真实API未启用；不能视为真实模型验证通过')
class LiveAPIIntegration(unittest.TestCase):
    def test_real_mathematical_planning(self):
        result=run_from_env(SMOKE_GOAL)
        self.assertEqual(result['status'],'plan_generated',result)
        self.assertGreaterEqual(result['real_model_responses'],1)
        self.assertEqual(result['evidence_kind'],'live')
        self.assertFalse(result['formal_goal_verified']);self.assertEqual(result['lean_status'],'not_run')
