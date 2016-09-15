require 'test_helper'

class ReportControllerTest < ActionDispatch::IntegrationTest
  test "should get mainpage" do
    get report_mainpage_url
    assert_response :success
  end

  test "should get new_report" do
    get report_new_report_url
    assert_response :success
  end

end
